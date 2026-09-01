#!/usr/bin/env python3
"""Render a recoverable fixed-16 restricted finite-D9 certificate bundle.

The input TSV is emitted by an untrusted Lean search executable.  This
renderer independently validates the full binary topology, every rational
cut, every terminal box, lower-first terminal numbering, and the fixed-16
root.  It then emits:

* one proof-free configuration module whose boxes are reconstructed from the
  root by exact lower/upper paths;
* configurable, independently recoverable arithmetic chunks in which one
  ``List.all`` receipt authenticates 32--128 terminal predicates and ordinary
  structural list lemmas recover the individual equalities;
* an arithmetic-free checked-tree assembly; and
* a semantic endpoint for the fixed-16 restricted ledger row.

Neither this script nor the input plan is proof authority.  Accepted leaves,
established physical/nonpositive-J discards, and exact ``k <= s`` wedge
discards are all replayed by Lean's ordinary kernel against the external box
reconstructed by the generic subdivision path.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass, replace
from fractions import Fraction
from pathlib import Path
from typing import Any, TypeAlias


sys.dont_write_bytecode = True


class GenerationError(RuntimeError):
    """The untrusted plan or requested output configuration is invalid."""


def fail(message: str) -> None:
    raise GenerationError(message)


SCRIPT = Path(__file__).resolve()
PLAN_FORMATS = {
    "fixed16-restricted-d9-plan-v1",
    "fixed16-restricted-d9-plan-v2",
}
SLAB_PLAN_FORMAT = "fixed16-restricted-d9-slab-plan-v1"
CHECKPOINT_PLAN_FORMAT = "fixed16-restricted-d9-checkpoint-plan-v1"
MANIFEST_FORMAT = "fixed16-restricted-d9-segmented-bundle-v2"
EXPECTED_ROOT = (
    Fraction(1, 16), Fraction(1, 10),
    Fraction(1, 16), Fraction(4),
    Fraction(0), Fraction(1),
)
PARAMETER_NAMES = ("terms", "sqrtFuel", "logFuel", "depth")
TERMINAL_KINDS = ("fallback", "centered", "irrelevant", "wedge")
ALLOWED_CHUNK_SIZES = (32, 64, 128)
DEFAULT_CHUNK_SIZE = 64
MAX_CHUNK_SIZE = max(ALLOWED_CHUNK_SIZES)
MAX_DEPTH = 64
# Direct-D9 pilots can still require several thousand terminals before the
# centered-mean evaluator is available.  These are hard corruption/resource
# guards, not target sizes; the production design should remain far smaller.
MAX_TERMINALS = 65536
MAX_PLAN_BYTES = 32 * 1024 * 1024
MAX_BUNDLE_BYTES = 128 * 1024 * 1024
MAX_RATIONAL_BITS = 4096

RATIONAL_RE = re.compile(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?")
PATH_RE = re.compile(r"r[LR]*")
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9]*(?:\.[A-Z][A-Za-z0-9]*)+")
NAMESPACE_RE = re.compile(r"[A-Z][A-Za-z0-9]*")
FORBIDDEN_LEAN_TOKENS = (
    "native_decide",
    "vm_decide",
    "ofReduceBool",
    "trustCompiler",
    "run_tac",
    "sorry",
    "admit",
)

def parse_nat(text: str, context: str) -> int:
    if not re.fullmatch(r"0|[1-9][0-9]*", text):
        fail(f"{context}: expected canonical natural, got {text!r}")
    return int(text)


def parse_rat(text: str, context: str) -> Fraction:
    if not RATIONAL_RE.fullmatch(text):
        fail(f"{context}: malformed rational {text!r}")
    value = Fraction(text)
    if str(value) != text:
        fail(f"{context}: noncanonical rational {text!r}; expected {value}")
    if (value.numerator.bit_length() > MAX_RATIONAL_BITS
            or value.denominator.bit_length() > MAX_RATIONAL_BITS):
        fail(f"{context}: rational exceeds {MAX_RATIONAL_BITS}-bit guard")
    return value


@dataclass(frozen=True, slots=True)
class Box:
    s_lo: Fraction
    s_hi: Fraction
    k_lo: Fraction
    k_hi: Fraction
    chi_lo: Fraction
    chi_hi: Fraction

    def lower(self, axis: str, cut: Fraction) -> "Box":
        if axis == "s":
            return Box(self.s_lo, cut, self.k_lo, self.k_hi,
                       self.chi_lo, self.chi_hi)
        if axis == "k":
            return Box(self.s_lo, self.s_hi, self.k_lo, cut,
                       self.chi_lo, self.chi_hi)
        if axis == "chi":
            return Box(self.s_lo, self.s_hi, self.k_lo, self.k_hi,
                       self.chi_lo, cut)
        fail(f"unknown certificate axis {axis!r}")

    def upper(self, axis: str, cut: Fraction) -> "Box":
        if axis == "s":
            return Box(cut, self.s_hi, self.k_lo, self.k_hi,
                       self.chi_lo, self.chi_hi)
        if axis == "k":
            return Box(self.s_lo, self.s_hi, cut, self.k_hi,
                       self.chi_lo, self.chi_hi)
        if axis == "chi":
            return Box(self.s_lo, self.s_hi, self.k_lo, self.k_hi,
                       cut, self.chi_hi)
        fail(f"unknown certificate axis {axis!r}")

    def bounds(self, axis: str) -> tuple[Fraction, Fraction]:
        if axis == "s":
            return self.s_lo, self.s_hi
        if axis == "k":
            return self.k_lo, self.k_hi
        if axis == "chi":
            return self.chi_lo, self.chi_hi
        fail(f"unknown certificate axis {axis!r}")

    def fields(self) -> tuple[Fraction, ...]:
        return (self.s_lo, self.s_hi, self.k_lo, self.k_hi,
                self.chi_lo, self.chi_hi)


@dataclass(frozen=True, slots=True)
class Split:
    path: str
    axis: str
    cut: Fraction


@dataclass(frozen=True, slots=True)
class Terminal:
    index: int
    path: str
    kind: str
    printed_box: Box


Node: TypeAlias = Split | Terminal


@dataclass(frozen=True, slots=True)
class Plan:
    parameters: tuple[int, int, int, int]
    root: Box
    nodes: dict[str, Node]
    boxes: dict[str, Box]
    terminals: tuple[Terminal, ...]
    source_sha256: str
    source_bytes: int
    input_sha256s: tuple[str, ...] = ()


def parse_box(fields: list[str], context: str) -> Box:
    if len(fields) != 6:
        fail(f"{context}: expected six box endpoints")
    values = tuple(parse_rat(value, f"{context} endpoint {index}")
                   for index, value in enumerate(fields))
    box = Box(*values)
    if not (box.s_lo <= box.s_hi and box.k_lo <= box.k_hi
            and box.chi_lo <= box.chi_hi):
        fail(f"{context}: inverted box")
    return box


def validate_path(path: str, context: str) -> None:
    if not PATH_RE.fullmatch(path):
        fail(f"{context}: invalid binary path {path!r}")


def parse_plan_bytes(raw: bytes) -> Plan:
    if len(raw) > MAX_PLAN_BYTES:
        fail(f"plan exceeds {MAX_PLAN_BYTES}-byte guard")
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        fail(f"plan is not ASCII: {error}")
    lines = text.splitlines()
    if not lines:
        fail("empty plan")
    header = lines[0].split("\t")
    if (len(header) != 12 or header[0] != "H"
            or header[1] not in PLAN_FORMATS):
        fail("invalid fixed16 restricted-D9 plan header")
    plan_format = header[1]
    parameters = tuple(
        parse_nat(value, f"header {PARAMETER_NAMES[index]}")
        for index, value in enumerate(header[2:6])
    )
    if parameters[-1] > MAX_DEPTH:
        fail(f"plan depth exceeds {MAX_DEPTH}")
    root = parse_box(header[6:], "root")
    if root.fields() != EXPECTED_ROOT:
        fail("plan root is not the exact clipped fixed-16 root")

    nodes: dict[str, Node] = {}
    terminals: list[Terminal] = []
    footer_count: int | None = None
    for line_number, line in enumerate(lines[1:], start=2):
        fields = line.split("\t")
        context = f"line {line_number}"
        if not fields or not fields[0]:
            fail(f"{context}: empty record")
        if footer_count is not None:
            fail(f"{context}: data after footer")
        if fields[0] == "E":
            if len(fields) != 2:
                fail(f"{context}: malformed footer")
            footer_count = parse_nat(fields[1], f"{context} count")
            continue
        if fields[0] == "F":
            fail(f"{context}: unresolved frontier; refusing Lean emission")
        if fields[0] == "N":
            if len(fields) != 4:
                fail(f"{context}: malformed split")
            node_path, axis = fields[1], fields[2]
            validate_path(node_path, context)
            if axis not in {"s", "k", "chi"}:
                fail(f"{context}: invalid axis {axis!r}")
            node: Node = Split(
                node_path, axis, parse_rat(fields[3], f"{context} cut")
            )
        elif fields[0] in {"A", "C", "X", "W"}:
            if len(fields) != 10:
                fail(f"{context}: malformed terminal")
            index = parse_nat(fields[1], f"{context} terminal index")
            node_path, printed_kind = fields[2], fields[3]
            validate_path(node_path, context)
            expected_kind = {
                "A": "accept" if plan_format.endswith("v1") else "fallback",
                "C": "centered",
                "X": "irrelevant",
                "W": "wedge",
            }[fields[0]]
            if fields[0] == "C" and plan_format.endswith("v1"):
                fail(f"{context}: centered terminal requires plan v2")
            if printed_kind != expected_kind:
                fail(f"{context}: terminal tag/kind mismatch")
            if expected_kind == "accept":
                expected_kind = "fallback"
            node = Terminal(index, node_path, expected_kind,
                            parse_box(fields[4:], f"{context} box"))
            terminals.append(node)
        else:
            fail(f"{context}: unknown record tag {fields[0]!r}")
        if node.path in nodes:
            fail(f"{context}: duplicate path {node.path}")
        nodes[node.path] = node

    if footer_count is None:
        fail("missing plan footer")
    if footer_count != len(terminals):
        fail(f"footer says {footer_count} terminals, parsed {len(terminals)}")
    if not terminals:
        fail("plan contains no terminals")
    if len(terminals) > MAX_TERMINALS:
        fail(f"terminal count exceeds {MAX_TERMINALS}")
    if [terminal.index for terminal in terminals] != list(range(len(terminals))):
        fail("terminal indices are not contiguous lower-first indices")
    if plan_format.endswith("v2"):
        forced = {
            "r": ("k", Fraction(1)),
            "rL": ("k", Fraction(1, 4)),
            "rLL": ("k", Fraction(1, 8)),
            "rLR": ("k", Fraction(1, 2)),
            "rR": ("k", Fraction(2)),
        }
        for forced_path, (axis, cut) in forced.items():
            node = nodes.get(forced_path)
            if not (isinstance(node, Split)
                    and node.axis == axis and node.cut == cut):
                fail(f"plan v2 is missing forced split {forced_path}")

    boxes: dict[str, Box] = {}
    preorder_terminals: list[int] = []
    visited: set[str] = set()
    depth = parameters[-1]

    def visit(node_path: str, expected: Box) -> None:
        if node_path not in nodes:
            fail(f"topology is missing path {node_path}")
        node = nodes[node_path]
        visited.add(node_path)
        boxes[node_path] = expected
        if isinstance(node, Split):
            node_depth = len(node_path) - 1
            if node_depth >= depth:
                fail(f"split {node_path} exceeds configured depth {depth}")
            lo, hi = expected.bounds(node.axis)
            if not lo < node.cut < hi:
                fail(f"split {node_path} cut is not strictly inside its box")
            visit(node_path + "L", expected.lower(node.axis, node.cut))
            visit(node_path + "R", expected.upper(node.axis, node.cut))
        else:
            if node.printed_box != expected:
                fail(f"terminal {node_path} box disagrees with its exact path")
            if node.kind == "wedge" and not expected.k_hi <= expected.s_lo:
                fail(f"wedge terminal {node_path} fails kHi <= sLo")
            if node.kind != "wedge" and expected.k_hi <= expected.s_lo:
                fail(f"terminal {node_path} bypasses the cheap wedge discard")
            preorder_terminals.append(node.index)

    visit("r", root)
    if visited != set(nodes):
        fail(f"plan has unreachable paths: {sorted(set(nodes) - visited)}")
    if preorder_terminals != list(range(len(terminals))):
        fail("terminal indices do not match lower-first preorder")
    split_count = sum(isinstance(node, Split) for node in nodes.values())
    if split_count + 1 != len(terminals):
        fail("topology is not a full binary tree")
    return Plan(parameters, root, nodes, boxes, tuple(terminals),
                hashlib.sha256(raw).hexdigest(), len(raw))


def parse_plan(path: Path) -> Plan:
    return parse_plan_bytes(path.read_bytes())


SLAB_PREFIXES = ("rLLL", "rLLR", "rLRL", "rLRR", "rRL", "rRR")
SLAB_K_BOUNDS = (
    (Fraction(1, 16), Fraction(1, 8)),
    (Fraction(1, 8), Fraction(1, 4)),
    (Fraction(1, 4), Fraction(1, 2)),
    (Fraction(1, 2), Fraction(1)),
    (Fraction(1), Fraction(2)),
    (Fraction(2), Fraction(4)),
)


def expected_slab_root(index: int) -> Box:
    k_lo, k_hi = SLAB_K_BOUNDS[index]
    return Box(Fraction(1, 16), Fraction(1, 10), k_lo, k_hi,
               Fraction(0), Fraction(1))


def merge_slab_plans(paths: list[Path]) -> Plan:
    """Authenticate and merge six independent checkpoint plans."""
    if len(paths) != 6:
        fail("exactly six --slab-plan files are required")
    transformed: list[list[str]] = []
    input_hashes: list[str] = []
    common_parameters: tuple[int, int, int] | None = None
    total_terminals = 0
    total_depth = 0
    for expected_index, path in enumerate(paths):
        raw = path.read_bytes()
        if len(raw) > MAX_PLAN_BYTES:
            fail(f"slab {expected_index}: plan exceeds byte guard")
        try:
            lines = raw.decode("ascii").splitlines()
        except UnicodeDecodeError as error:
            fail(f"slab {expected_index}: plan is not ASCII: {error}")
        if not lines:
            fail(f"slab {expected_index}: empty plan")
        header = lines[0].split("\t")
        if (len(header) != 13
                or header[:2] != ["H", SLAB_PLAN_FORMAT]):
            fail(f"slab {expected_index}: invalid checkpoint header")
        slab_index = parse_nat(header[2], f"slab {expected_index} index")
        if slab_index != expected_index:
            fail(f"slab checkpoint order mismatch: expected {expected_index}")
        parameters = tuple(parse_nat(value,
                                     f"slab {expected_index} parameter")
                           for value in header[3:7])
        if parameters[-1] > MAX_DEPTH:
            fail(f"slab {expected_index}: adaptive depth exceeds guard")
        slab_root = parse_box(header[7:], f"slab {expected_index} root")
        if slab_root != expected_slab_root(expected_index):
            fail(f"slab {expected_index}: root does not match forced k slab")
        if common_parameters is None:
            common_parameters = parameters[:3]
        elif parameters[:3] != common_parameters:
            fail("slab evaluator parameters disagree")
        prefix = SLAB_PREFIXES[expected_index]
        local_records: list[str] = []
        local_terminal_count = 0
        footer_count: int | None = None
        for line_number, line in enumerate(lines[1:], start=2):
            fields = line.split("\t")
            context = f"slab {expected_index} line {line_number}"
            if footer_count is not None:
                fail(f"{context}: data after footer")
            if fields[0] == "E":
                if len(fields) != 2:
                    fail(f"{context}: malformed footer")
                footer_count = parse_nat(fields[1], f"{context} count")
                continue
            if fields[0] == "N":
                if len(fields) != 4:
                    fail(f"{context}: malformed split")
                validate_path(fields[1], context)
                fields[1] = prefix + fields[1][1:]
            elif fields[0] in {"A", "C", "X", "W"}:
                if len(fields) != 10:
                    fail(f"{context}: malformed terminal")
                local_index = parse_nat(fields[1], f"{context} index")
                if local_index != local_terminal_count:
                    fail(f"{context}: noncontiguous local terminal index")
                validate_path(fields[2], context)
                fields[1] = str(total_terminals + local_terminal_count)
                fields[2] = prefix + fields[2][1:]
                local_terminal_count += 1
            else:
                fail(f"{context}: unknown record tag {fields[0]!r}")
            local_records.append("\t".join(fields))
        if footer_count is None or footer_count != local_terminal_count:
            fail(f"slab {expected_index}: footer/terminal count mismatch")
        transformed.append(local_records)
        total_terminals += local_terminal_count
        total_depth = max(total_depth, parameters[-1] + len(prefix) - 1)
        input_hashes.append(hashlib.sha256(raw).hexdigest())
    assert common_parameters is not None
    root_fields = [str(value) for value in EXPECTED_ROOT]
    header = "\t".join([
        "H", "fixed16-restricted-d9-plan-v2",
        *(str(value) for value in common_parameters), str(total_depth),
        *root_fields,
    ])
    forced_and_slab_records = [
        "N\tr\tk\t1",
        "N\trL\tk\t1/4",
        "N\trLL\tk\t1/8",
        *transformed[0], *transformed[1],
        "N\trLR\tk\t1/2",
        *transformed[2], *transformed[3],
        "N\trR\tk\t2",
        *transformed[4], *transformed[5],
    ]
    merged = ("\n".join([
        header, *forced_and_slab_records, f"E\t{total_terminals}", ""
    ])).encode("ascii")
    return replace(parse_plan_bytes(merged),
                   input_sha256s=tuple(input_hashes))


def checkpoint_skeleton(
    level: int, root: Box, prefix: str = "r",
) -> tuple[list[Split], list[tuple[str, Box]]]:
    """Reconstruct the generator's fixed 16-way checkpoint partition.

    One level bisects ``s`` and ``k`` and quarters ``chi``.  The quartering is
    represented by the balanced binary cuts ``1/2`` followed by ``1/4`` and
    ``3/4``; its lower-first leaves are exactly the order returned by the Lean
    generator's ``fixedCellRoots``.  Recursing at each leaf therefore gives
    the exact ``16^level`` checkpoint path/root pairs without trusting names
    or printed boxes from the directory.
    """
    if level < 0 or level > 3:
        fail("checkpoint level must lie in 0..3")
    if level == 0:
        return [], [(prefix, root)]

    splits: list[Split] = []
    cells: list[tuple[str, Box]] = []
    s_cut = sum(root.bounds("s"), Fraction(0)) / 2
    splits.append(Split(prefix, "s", s_cut))
    for s_branch, s_box in (
        ("L", root.lower("s", s_cut)),
        ("R", root.upper("s", s_cut)),
    ):
        s_path = prefix + s_branch
        k_cut = sum(s_box.bounds("k"), Fraction(0)) / 2
        splits.append(Split(s_path, "k", k_cut))
        for k_branch, k_box in (
            ("L", s_box.lower("k", k_cut)),
            ("R", s_box.upper("k", k_cut)),
        ):
            k_path = s_path + k_branch
            chi_lo, chi_hi = k_box.bounds("chi")
            chi_half = (chi_lo + chi_hi) / 2
            chi_one = chi_lo + (chi_hi - chi_lo) / 4
            chi_three = chi_lo + 3 * (chi_hi - chi_lo) / 4
            splits.append(Split(k_path, "chi", chi_half))
            splits.append(Split(k_path + "L", "chi", chi_one))
            splits.append(Split(k_path + "R", "chi", chi_three))
            cells.extend([
                (k_path + "LL", k_box.lower("chi", chi_one)),
                (k_path + "LR", k_box.upper("chi", chi_one).lower(
                    "chi", chi_half)),
                (k_path + "RL", k_box.upper("chi", chi_half).lower(
                    "chi", chi_three)),
                (k_path + "RR", k_box.upper("chi", chi_three)),
            ])

    leaves: list[tuple[str, Box]] = []
    for cell_path, cell_root in cells:
        child_splits, child_leaves = checkpoint_skeleton(
            level - 1, cell_root, cell_path
        )
        splits.extend(child_splits)
        leaves.extend(child_leaves)
    return splits, leaves


def checkpoint_header(path: Path) -> tuple[
    bytes, list[str], int, int, int, tuple[int, int, int, int], Box
]:
    raw = path.read_bytes()
    if len(raw) > MAX_PLAN_BYTES:
        fail(f"checkpoint {path}: plan exceeds byte guard")
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        fail(f"checkpoint {path}: plan is not ASCII: {error}")
    if not lines:
        fail(f"checkpoint {path}: empty plan")
    header = lines[0].split("\t")
    if (len(header) != 15
            or header[:2] != ["H", CHECKPOINT_PLAN_FORMAT]):
        fail(f"checkpoint {path}: invalid header")
    slab_index = parse_nat(header[2], f"checkpoint {path} slab")
    level = parse_nat(header[3], f"checkpoint {path} level")
    checkpoint_index = parse_nat(header[4], f"checkpoint {path} index")
    parameters = tuple(
        parse_nat(value, f"checkpoint {path} parameter")
        for value in header[5:9]
    )
    if parameters[-1] > MAX_DEPTH:
        fail(f"checkpoint {path}: adaptive depth exceeds guard")
    root = parse_box(header[9:], f"checkpoint {path} root")
    return (raw, lines, slab_index, level, checkpoint_index,
            parameters, root)


def merge_checkpoint_directory(directory: Path) -> Plan:
    """Authenticate and merge a complete fixed-level checkpoint directory."""
    if not directory.is_dir():
        fail(f"checkpoint directory does not exist: {directory}")
    paths = sorted(directory.glob("*.tsv"))
    if not paths:
        fail("checkpoint directory contains no TSV plans")

    entries: dict[tuple[int, int], tuple[Path, bytes, list[str], Box]] = {}
    common_level: int | None = None
    common_parameters: tuple[int, int, int, int] | None = None
    for path in paths:
        raw, lines, slab_index, level, checkpoint_index, parameters, root = \
            checkpoint_header(path)
        if slab_index >= len(SLAB_PREFIXES):
            fail(f"checkpoint {path}: slab index must lie in 0..5")
        if common_level is None:
            common_level = level
        elif level != common_level:
            fail("checkpoint files use different fixed partition levels")
        if common_parameters is None:
            common_parameters = parameters
        elif parameters != common_parameters:
            fail("checkpoint evaluator parameters disagree")
        key = (slab_index, checkpoint_index)
        if key in entries:
            fail(f"duplicate checkpoint slab={slab_index} index={checkpoint_index}")
        entries[key] = (path, raw, lines, root)

    assert common_level is not None and common_parameters is not None
    expected_per_slab = 16 ** common_level
    expected_keys = {
        (slab_index, checkpoint_index)
        for slab_index in range(6)
        for checkpoint_index in range(expected_per_slab)
    }
    missing = sorted(expected_keys - set(entries))
    extra = sorted(set(entries) - expected_keys)
    if missing or extra:
        fail("checkpoint directory is incomplete or has out-of-range indices: "
             f"missing={missing[:8]} extra={extra[:8]}")

    transformed: list[list[str]] = []
    input_hashes: list[str] = []
    total_terminals = 0
    total_depth = 0
    for slab_index in range(6):
        slab_prefix = SLAB_PREFIXES[slab_index]
        skeleton, leaves = checkpoint_skeleton(
            common_level, expected_slab_root(slab_index)
        )
        slab_records = [
            "\t".join(["N", slab_prefix + split.path[1:],
                       split.axis, str(split.cut)])
            for split in skeleton
        ]
        for checkpoint_index, (checkpoint_path, checkpoint_root) in enumerate(leaves):
            path, raw, lines, printed_root = entries[
                (slab_index, checkpoint_index)
            ]
            if printed_root != checkpoint_root:
                fail(f"checkpoint {path}: root disagrees with fixed skeleton")
            full_prefix = slab_prefix + checkpoint_path[1:]
            local_terminal_count = 0
            footer_count: int | None = None
            for line_number, line in enumerate(lines[1:], start=2):
                fields = line.split("\t")
                context = f"checkpoint {path} line {line_number}"
                if footer_count is not None:
                    fail(f"{context}: data after footer")
                if fields[0] == "E":
                    if len(fields) != 2:
                        fail(f"{context}: malformed footer")
                    footer_count = parse_nat(fields[1], f"{context} count")
                    continue
                if fields[0] == "N":
                    if len(fields) != 4:
                        fail(f"{context}: malformed split")
                    validate_path(fields[1], context)
                    fields[1] = full_prefix + fields[1][1:]
                elif fields[0] in {"A", "C", "X", "W"}:
                    if len(fields) != 10:
                        fail(f"{context}: malformed terminal")
                    local_index = parse_nat(fields[1], f"{context} index")
                    if local_index != local_terminal_count:
                        fail(f"{context}: noncontiguous local terminal index")
                    validate_path(fields[2], context)
                    fields[1] = str(total_terminals + local_terminal_count)
                    fields[2] = full_prefix + fields[2][1:]
                    local_terminal_count += 1
                else:
                    fail(f"{context}: unknown record tag {fields[0]!r}")
                slab_records.append("\t".join(fields))
            if footer_count is None or footer_count != local_terminal_count:
                fail(f"checkpoint {path}: footer/terminal count mismatch")
            total_terminals += local_terminal_count
            total_depth = max(
                total_depth, common_parameters[-1] + len(full_prefix) - 1
            )
            input_hashes.append(hashlib.sha256(raw).hexdigest())
        transformed.append(slab_records)

    root_fields = [str(value) for value in EXPECTED_ROOT]
    header = "\t".join([
        "H", "fixed16-restricted-d9-plan-v2",
        *(str(value) for value in common_parameters[:3]), str(total_depth),
        *root_fields,
    ])
    forced_and_checkpoint_records = [
        "N\tr\tk\t1",
        "N\trL\tk\t1/4",
        "N\trLL\tk\t1/8",
        *transformed[0], *transformed[1],
        "N\trLR\tk\t1/2",
        *transformed[2], *transformed[3],
        "N\trR\tk\t2",
        *transformed[4], *transformed[5],
    ]
    merged = ("\n".join([
        header, *forced_and_checkpoint_records,
        f"E\t{total_terminals}", "",
    ])).encode("ascii")
    return replace(parse_plan_bytes(merged),
                   input_sha256s=tuple(input_hashes))


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def config_source(plan: Plan, namespace: str, generator_sha256: str) -> str:
    parameters = "\n".join(
        f"def {name} : Nat := {value}"
        for name, value in zip(PARAMETER_NAMES, plan.parameters, strict=True)
    )
    split_paths = sorted(
        (path for path, node in plan.nodes.items() if isinstance(node, Split)),
        key=lambda item: (len(item), item),
    )
    cut_definitions = "\n".join(
        f"def cut_{path} : ℚ := {lean_rat(plan.nodes[path].cut)}"
        for path in split_paths
    )
    box_definitions = [
        "abbrev rootBox : CertificateBox :=\n"
        "  lrDeterminantFixed16KLeFourRoot",
        "abbrev box_r : CertificateBox := rootBox",
    ]
    for path in split_paths:
        split = plan.nodes[path]
        assert isinstance(split, Split)
        box_definitions.extend((
            f"def box_{path}L : CertificateBox :=\n"
            f"  box_{path}.lower .{split.axis} cut_{path}",
            f"def box_{path}R : CertificateBox :=\n"
            f"  box_{path}.upper .{split.axis} cut_{path}",
        ))
    boxes = "\n\n".join(box_definitions)
    return f"""import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteD9HybridCheckedTree

/-!
Untrusted fixed-16 restricted-D9 topology data.  Every box below is derived
from the exact clipped root by its subdivision path; terminal arithmetic is
checked only in the generated chunks.

Plan SHA-256: {plan.source_sha256}
Generator SHA-256: {generator_sha256}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

def planSha256 : String := "{plan.source_sha256}"
def generatorSha256 : String := "{generator_sha256}"

{parameters}

abbrev CheckedTree (root : CertificateBox) : Type :=
  LRFiniteDeterminantRestrictedD9HybridPayloadFree.CheckedTree
    terms sqrtFuel logFuel root

{cut_definitions}

{boxes}

end {namespace}
end CourtadeKumar
"""


def terminal_predicate(terminal: Terminal) -> str:
    """The exact external-box Boolean placed in a chunk's `List.all`."""
    box_name = f"box_{terminal.path}"
    if terminal.kind == "fallback":
        return (
            "LRFiniteDeterminantRestrictedD9HybridPayloadFree.acceptCheck "
            f"terms sqrtFuel logFuel {box_name} .fallback"
        )
    if terminal.kind == "centered":
        return (
            "LRFiniteDeterminantRestrictedD9HybridPayloadFree.acceptCheck "
            f"terms sqrtFuel logFuel {box_name} .centered"
        )
    if terminal.kind in {"irrelevant", "wedge"}:
        return (
            "LRFiniteDeterminantRestrictedD9HybridPayloadFree.discardCheck "
            f"terms sqrtFuel logFuel {box_name} ()"
        )
    fail(f"terminal {terminal.index}: unknown kind {terminal.kind!r}")


def terminal_from_receipt(terminal: Terminal, chunk_stem: str,
                          local_index: int, chunk_length: int) -> str:
    """Project one leaf equality structurally and package its checked tree."""
    stem = f"leaf{terminal.index:04d}"
    box_name = f"box_{terminal.path}"
    predicate = terminal_predicate(terminal)
    projection = (
        f"(List.all_eq_true.mp {chunk_stem}Receipt) {local_index}\n"
        "      (List.mem_range.mpr (by decide))"
    )
    if terminal.kind == "fallback":
        package = (
            "LRFiniteDeterminantRestrictedD9HybridPayloadFree.CheckedTree."
            "ofAccept\n"
            f"    terms sqrtFuel logFuel .fallback\n    {projection}"
        )
        bridge = ""
    elif terminal.kind == "centered":
        package = (
            "LRFiniteDeterminantRestrictedD9HybridPayloadFree.CheckedTree."
            "ofAccept\n"
            f"    terms sqrtFuel logFuel .centered\n    {projection}"
        )
        bridge = ""
    elif terminal.kind in {"irrelevant", "wedge"}:
        bridge = ""
        package = (
            "LRFiniteDeterminantRestrictedD9HybridPayloadFree.CheckedTree."
            "ofDiscard\n"
            f"    terms sqrtFuel logFuel\n    {projection}"
        )
    else:
        fail(f"terminal {terminal.index}: unknown kind {terminal.kind!r}")
    return f"""/- Terminal {terminal.index}, path {terminal.path}, kind {terminal.kind};
projected at local index {local_index} of {chunk_length}. -/
{bridge}
def {stem}Checked : CheckedTree {box_name} :=
  {package}"""


def chunk_source(plan: Plan, terminals: tuple[Terminal, ...],
                 chunk_index: int, module_prefix: str,
                 namespace: str) -> str:
    if not terminals:
        fail("refusing to render an empty terminal chunk")
    chunk_stem = f"chunk{chunk_index:03d}"
    predicate_cases = "\n".join(
        f"  | {local_index} => {terminal_predicate(terminal)}"
        for local_index, terminal in enumerate(terminals)
    )
    projections = "\n\n".join(
        terminal_from_receipt(terminal, chunk_stem, local_index,
                              len(terminals))
        for local_index, terminal in enumerate(terminals)
    )
    indices = [item.index for item in terminals]
    return f"""import {module_prefix}.Config
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
Recoverable kernel replay chunk {chunk_index:03d}; terminals {indices}.
Plan SHA-256: {plan.source_sha256}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

def {chunk_stem}Predicate : Nat → Bool
{predicate_cases}
  | _ => false

def {chunk_stem}Result : Bool :=
  (List.range {len(terminals)}).all {chunk_stem}Predicate

#kernel_checked_bool {chunk_stem}Receipt {chunk_stem}Result

{projections}

end {namespace}
end CourtadeKumar
"""


def chunk_groups(terminals: tuple[Terminal, ...],
                 chunk_size: int) -> list[tuple[Terminal, ...]]:
    if chunk_size not in ALLOWED_CHUNK_SIZES:
        fail(f"chunk size must be one of {ALLOWED_CHUNK_SIZES}")
    groups = [terminals[start:start + chunk_size]
              for start in range(0, len(terminals), chunk_size)]
    if tuple(item for group in groups for item in group) != terminals:
        fail("chunk partition lost or reordered a terminal")
    return groups


def assembly_source(plan: Plan, chunk_count: int, module_prefix: str,
                    namespace: str) -> str:
    imports = "\n".join(
        f"import {module_prefix}.Chunk{index:03d}"
        for index in range(chunk_count)
    )
    terminal_names = {
        terminal.path: f"leaf{terminal.index:04d}Checked"
        for terminal in plan.terminals
    }
    definitions: list[str] = []
    split_paths = sorted(
        (path for path, node in plan.nodes.items() if isinstance(node, Split)),
        key=lambda item: (-len(item), item),
    )
    for path in split_paths:
        split = plan.nodes[path]
        assert isinstance(split, Split)
        lower_path, upper_path = path + "L", path + "R"
        lower = terminal_names.get(lower_path, f"node_{lower_path}")
        upper = terminal_names.get(upper_path, f"node_{upper_path}")
        definitions.append(f"""def node_{path} : CheckedTree box_{path} :=
  LRFiniteDeterminantRestrictedD9HybridPayloadFree.CheckedTree.join
    .{split.axis} cut_{path} {lower} {upper}""")
    body = "\n\n".join(definitions)
    root_name = terminal_names.get("r", "node_r")
    return f"""{imports}

/-!
Arithmetic-free assembly of all independently kernel-checked terminals.
The exact lower/upper path boxes are reconstructed in Config.
Plan SHA-256: {plan.source_sha256}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

{body}

abbrev checkedRoot : CheckedTree rootBox := {root_name}

abbrev certificate : LRFiniteDeterminantRestrictedD9HybridPayloadFree.Tree :=
  checkedRoot.certificate

theorem certificateCheck :
    certificate.check
      (LRFiniteDeterminantRestrictedD9HybridPayloadFree.acceptCheck
        terms sqrtFuel logFuel)
      (LRFiniteDeterminantRestrictedD9HybridPayloadFree.discardCheck
        terms sqrtFuel logFuel) rootBox = true :=
  checkedRoot.checked

end {namespace}
end CourtadeKumar
"""


def certificate_source(plan: Plan, module_prefix: str,
                       namespace: str) -> str:
    return f"""import {module_prefix}.Assembly

/-!
Semantic endpoint of the generated fixed-16 restricted-D9 certificate.
All arithmetic enters through the terminal kernel receipts imported by
Assembly; this module performs no certificate computation.
Plan SHA-256: {plan.source_sha256}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

def restrictedSemanticTree :
    LRFiniteDeterminantRestrictedSemanticD9CheckedTree
    lrDeterminantFixed16KLeFourRoot :=
  checkedRoot.toSemanticCheckedTree

theorem restrictedCertificate :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantFixed16Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point :=
  lrDeterminantFixed16KLeFourRegion_certificate_of_semanticD9Tree
    restrictedSemanticTree

end {namespace}
end CourtadeKumar
"""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True,
                       separators=(",", ": ")) + "\n").encode("ascii")


def validate_sources(plan: Plan, sources: dict[str, bytes]) -> None:
    if not sources:
        fail("renderer produced no Lean sources")
    joined = b"\n".join(sources[name] for name in sorted(sources))
    for token in FORBIDDEN_LEAN_TOKENS:
        if token.encode("ascii") in joined:
            fail(f"generated Lean contains forbidden token {token!r}")
    chunk_count = sum(name.startswith("Chunk") for name in sources)
    if joined.count(b"#kernel_checked_bool") != chunk_count:
        fail("generated Lean does not contain exactly one receipt per chunk")
    if joined.count(b"List.all_eq_true.mp") != len(plan.terminals):
        fail("generated Lean does not structurally project every terminal")
    if joined.count(b"CheckedTree.join") != sum(
            isinstance(node, Split) for node in plan.nodes.values()):
        fail("generated assembly join count does not match topology")
    for terminal in plan.terminals:
        box_name = f"box_{terminal.path}".encode("ascii")
        stem = f"leaf{terminal.index:04d}Checked".encode("ascii")
        if box_name not in joined or stem not in joined:
            fail(f"terminal {terminal.index}: missing external path binding")
    if sum(len(source) for source in sources.values()) > MAX_BUNDLE_BYTES:
        fail(f"generated Lean exceeds {MAX_BUNDLE_BYTES}-byte guard")


def render_sources(plan: Plan, chunk_size: int, module_prefix: str,
                   namespace: str,
                   generator_sha256: str) -> tuple[dict[str, bytes],
                                                    list[tuple[Terminal, ...]]]:
    groups = chunk_groups(plan.terminals, chunk_size)
    text_sources: dict[str, str] = {
        "Config.lean": config_source(plan, namespace, generator_sha256),
    }
    for index, group in enumerate(groups):
        text_sources[f"Chunk{index:03d}.lean"] = chunk_source(
            plan, group, index, module_prefix, namespace
        )
    text_sources["Assembly.lean"] = assembly_source(
        plan, len(groups), module_prefix, namespace
    )
    text_sources["Certificate.lean"] = certificate_source(
        plan, module_prefix, namespace
    )
    sources = {name: text.encode("utf-8")
               for name, text in text_sources.items()}
    validate_sources(plan, sources)
    return sources, groups


def bundle_manifest(plan: Plan, sources: dict[str, bytes],
                    groups: list[tuple[Terminal, ...]], chunk_size: int,
                    module_prefix: str, namespace: str,
                    generator_sha256: str) -> tuple[dict[str, Any], str]:
    terminal_kinds = {
        kind: sum(terminal.kind == kind for terminal in plan.terminals)
        for kind in TERMINAL_KINDS
    }
    files = [
        {"path": name, "bytes": len(source),
         "sha256": hashlib.sha256(source).hexdigest()}
        for name, source in sorted(sources.items())
    ]
    core: dict[str, Any] = {
        "format": MANIFEST_FORMAT,
        "untrustedGenerator": True,
        "generatorSha256": generator_sha256,
        "planSha256": plan.source_sha256,
        "inputPlanSha256s": list(plan.input_sha256s),
        "planBytes": plan.source_bytes,
        "parameters": dict(zip(PARAMETER_NAMES, plan.parameters, strict=True)),
        "root": [str(value) for value in plan.root.fields()],
        "terminalCount": len(plan.terminals),
        "splitCount": sum(isinstance(node, Split)
                          for node in plan.nodes.values()),
        "terminalKinds": terminal_kinds,
        "chunkSize": chunk_size,
        "chunkCount": len(groups),
        "receiptStrategy": "list-all-one-kernel-receipt-per-chunk",
        "modulePrefix": module_prefix,
        "namespace": namespace,
        "chunks": [
            {
                "module": f"{module_prefix}.Chunk{index:03d}",
                "path": f"Chunk{index:03d}.lean",
                "terminals": [terminal.index for terminal in group],
                "paths": [terminal.path for terminal in group],
                "kinds": [terminal.kind for terminal in group],
            }
            for index, group in enumerate(groups)
        ],
        "assemblyModule": f"{module_prefix}.Assembly",
        "certificateModule": f"{module_prefix}.Certificate",
        "files": files,
    }
    bundle_sha256 = hashlib.sha256(canonical_json_bytes(core)).hexdigest()
    return {**core, "bundleSha256": bundle_sha256}, bundle_sha256


def atomic_write(path: Path, data: bytes, force: bool) -> None:
    if path.exists():
        if path.read_bytes() == data:
            return
        if not force:
            fail(f"refusing to replace differing {path}; pass --force")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".building")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def atomic_write_bundle(directory: Path, files: dict[str, bytes],
                        force: bool) -> None:
    """Preflight the complete owned bundle before replacing any file."""
    if directory.exists() and not directory.is_dir():
        fail(f"bundle output is not a directory: {directory}")
    for name, data in files.items():
        path = directory / name
        if path.exists() and path.read_bytes() != data and not force:
            fail(f"refusing to replace differing {path}; pass --force")
    directory.mkdir(parents=True, exist_ok=True)
    for name, data in files.items():
        atomic_write(directory / name, data, force)


def generate(args: argparse.Namespace) -> dict[str, Any]:
    if not MODULE_RE.fullmatch(args.module_prefix):
        fail("--module-prefix must be a dotted Lean module name")
    if not NAMESPACE_RE.fullmatch(args.namespace):
        fail("--namespace must be one Lean namespace identifier")
    if args.checkpoint_dir is not None:
        if args.plan is not None or args.slab_plan:
            fail("pass a full plan, slab plans, or a checkpoint directory")
        plan = merge_checkpoint_directory(args.checkpoint_dir)
    elif args.slab_plan:
        if args.plan is not None:
            fail("pass either one full plan or six --slab-plan files, not both")
        plan = merge_slab_plans(args.slab_plan)
    else:
        if args.plan is None:
            fail("a full plan or six --slab-plan files are required")
        plan = parse_plan(args.plan)
    generator_sha256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
    sources, groups = render_sources(
        plan, args.chunk_size, args.module_prefix, args.namespace,
        generator_sha256,
    )
    manifest, bundle_sha256 = bundle_manifest(
        plan, sources, groups, args.chunk_size, args.module_prefix,
        args.namespace, generator_sha256,
    )
    files = {**sources, "manifest.json": canonical_json_bytes(manifest)}
    if sum(len(data) for data in files.values()) > MAX_BUNDLE_BYTES:
        fail(f"bundle exceeds {MAX_BUNDLE_BYTES}-byte guard")
    atomic_write_bundle(args.output_dir, files, args.force)
    summary = {
        "bundleSha256": bundle_sha256,
        "chunkCount": len(groups),
        "chunkSize": args.chunk_size,
        "outputBytes": sum(len(data) for data in files.values()),
        "planSha256": plan.source_sha256,
        "splitCount": manifest["splitCount"],
        "terminalCount": len(plan.terminals),
        "terminalKinds": manifest["terminalKinds"],
    }
    print(json.dumps(summary, sort_keys=True))
    return summary


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("plan", type=Path, nargs="?",
                        help="canonical TSV plan emitted by the Lean search")
    result.add_argument(
        "--slab-plan", type=Path, action="append", default=[],
        help=("one independent slab checkpoint; pass six times in slab-index "
              "order to merge the forced topology"),
    )
    result.add_argument(
        "--checkpoint-dir", type=Path,
        help=("directory containing a complete fixed-level family of "
              "checkpoint TSV plans for all six slabs"),
    )
    result.add_argument("--output-dir", type=Path, required=True)
    result.add_argument("--module-prefix", required=True)
    result.add_argument("--namespace", required=True)
    result.add_argument("--chunk-size", type=int,
                        choices=ALLOWED_CHUNK_SIZES,
                        default=DEFAULT_CHUNK_SIZE)
    result.add_argument("--force", action="store_true")
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        generate(args)
    except (GenerationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
