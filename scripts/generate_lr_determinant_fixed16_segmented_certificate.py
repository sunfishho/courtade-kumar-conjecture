#!/usr/bin/env python3
"""Render a recoverable fixed-16 restricted finite-D9 certificate bundle.

The input TSV is emitted by an untrusted Lean search executable.  This
renderer independently validates the full binary topology, every rational
cut, every terminal box, lower-first terminal numbering, and the fixed-16
root.  It then emits:

* one proof-free configuration module whose boxes are reconstructed from the
  root by exact lower/upper paths;
* configurable, independently recoverable arithmetic chunks in which every
  terminal has its own ``#kernel_checked_bool`` receipt;
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
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, TypeAlias


sys.dont_write_bytecode = True


class GenerationError(RuntimeError):
    """The untrusted plan or requested output configuration is invalid."""


def fail(message: str) -> None:
    raise GenerationError(message)


SCRIPT = Path(__file__).resolve()
PLAN_FORMAT = "fixed16-restricted-d9-plan-v1"
MANIFEST_FORMAT = "fixed16-restricted-d9-segmented-bundle-v1"
EXPECTED_ROOT = (
    Fraction(1, 16), Fraction(1, 10),
    Fraction(1, 16), Fraction(4),
    Fraction(0), Fraction(1),
)
PARAMETER_NAMES = ("terms", "sqrtFuel", "logFuel", "depth")
TERMINAL_KINDS = ("accept", "irrelevant", "wedge")
DEFAULT_CHUNK_SIZE = 4
MAX_CHUNK_SIZE = 16
MAX_DEPTH = 32
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


def parse_plan(path: Path) -> Plan:
    raw = path.read_bytes()
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
    if len(header) != 12 or header[:2] != ["H", PLAN_FORMAT]:
        fail("invalid fixed16 restricted-D9 plan header")
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
        elif fields[0] in {"A", "X", "W"}:
            if len(fields) != 10:
                fail(f"{context}: malformed terminal")
            index = parse_nat(fields[1], f"{context} terminal index")
            node_path, printed_kind = fields[2], fields[3]
            validate_path(node_path, context)
            expected_kind = {"A": "accept", "X": "irrelevant",
                             "W": "wedge"}[fields[0]]
            if printed_kind != expected_kind:
                fail(f"{context}: terminal tag/kind mismatch")
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
    return f"""import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteD9CheckedTree

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
  LRFiniteDeterminantRestrictedD9PayloadFree.CheckedTree
    terms sqrtFuel logFuel root

{cut_definitions}

{boxes}

end {namespace}
end CourtadeKumar
"""


def terminal_declaration(terminal: Terminal) -> str:
    stem = f"leaf{terminal.index:04d}"
    box_name = f"box_{terminal.path}"
    if terminal.kind == "accept":
        predicate = (
            "LRFiniteDeterminantD9PayloadFree.accepts\n"
            f"    terms sqrtFuel logFuel {box_name} ()"
        )
        package = (
            "LRFiniteDeterminantRestrictedD9PayloadFree.CheckedTree.ofAccept\n"
            f"    terms sqrtFuel logFuel {stem}Check"
        )
        bridge = ""
        check_name = f"{stem}Check"
    elif terminal.kind == "irrelevant":
        predicate = (
            "LRFiniteDeterminantD9PayloadFree.discardCheck\n"
            f"    terms sqrtFuel logFuel {box_name} ()"
        )
        bridge = f"""
theorem {stem}RestrictedCheck :
    LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck
      terms sqrtFuel logFuel {box_name} () = true := by
  simp only [LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck,
    {stem}Check, Bool.or_true]
"""
        package = (
            "LRFiniteDeterminantRestrictedD9PayloadFree.CheckedTree.ofDiscard\n"
            f"    terms sqrtFuel logFuel {stem}RestrictedCheck"
        )
        check_name = f"{stem}Check"
    elif terminal.kind == "wedge":
        predicate = (
            "LRFiniteDeterminantRestrictedD9PayloadFree.geometricDiscardCheck\n"
            f"    {box_name}"
        )
        bridge = f"""
theorem {stem}RestrictedCheck :
    LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck
      terms sqrtFuel logFuel {box_name} () = true := by
  simp only [LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck,
    {stem}Check, Bool.true_or]
"""
        package = (
            "LRFiniteDeterminantRestrictedD9PayloadFree.CheckedTree.ofDiscard\n"
            f"    terms sqrtFuel logFuel {stem}RestrictedCheck"
        )
        check_name = f"{stem}Check"
    else:
        fail(f"terminal {terminal.index}: unknown kind {terminal.kind!r}")
    return f"""/- Terminal {terminal.index}, path {terminal.path}, kind {terminal.kind}. -/
def {stem}Result : Bool :=
  {predicate}

#kernel_checked_bool {check_name} {stem}Result
{bridge}
def {stem}Checked : CheckedTree {box_name} :=
  {package}"""


def chunk_source(plan: Plan, terminals: tuple[Terminal, ...],
                 chunk_index: int, module_prefix: str,
                 namespace: str) -> str:
    if not terminals:
        fail("refusing to render an empty terminal chunk")
    declarations = "\n\n".join(terminal_declaration(item) for item in terminals)
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

{declarations}

end {namespace}
end CourtadeKumar
"""


def chunk_groups(terminals: tuple[Terminal, ...],
                 chunk_size: int) -> list[tuple[Terminal, ...]]:
    if not 1 <= chunk_size <= MAX_CHUNK_SIZE:
        fail(f"chunk size must lie in [1, {MAX_CHUNK_SIZE}]")
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
  LRFiniteDeterminantRestrictedD9PayloadFree.CheckedTree.join
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

abbrev certificate : LRFiniteDeterminantD9PayloadFree.Tree :=
  checkedRoot.certificate

theorem certificateCheck :
    certificate.check
      (LRFiniteDeterminantD9PayloadFree.accepts terms sqrtFuel logFuel)
      (LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck
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

def restrictedRawTree : LRFiniteDeterminantRestrictedRawD9CheckedTree
    lrDeterminantFixed16KLeFourRoot :=
  checkedRoot.toRawCheckedTree

theorem restrictedCertificate :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantFixed16Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point :=
  lrDeterminantFixed16KLeFourRegion_certificate_of_restrictedD9Tree
    restrictedRawTree

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
    if joined.count(b"#kernel_checked_bool") != len(plan.terminals):
        fail("generated Lean does not contain one kernel receipt per terminal")
    if joined.count(b"CheckedTree.join") != sum(
            isinstance(node, Split) for node in plan.nodes.values()):
        fail("generated assembly join count does not match topology")
    for terminal in plan.terminals:
        box_name = f"box_{terminal.path}".encode("ascii")
        stem = f"leaf{terminal.index:04d}Result".encode("ascii")
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
        "planBytes": plan.source_bytes,
        "parameters": dict(zip(PARAMETER_NAMES, plan.parameters, strict=True)),
        "root": [str(value) for value in plan.root.fields()],
        "terminalCount": len(plan.terminals),
        "splitCount": sum(isinstance(node, Split)
                          for node in plan.nodes.values()),
        "terminalKinds": terminal_kinds,
        "chunkSize": chunk_size,
        "chunkCount": len(groups),
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
    result.add_argument("plan", type=Path,
                        help="canonical TSV plan emitted by the Lean search")
    result.add_argument("--output-dir", type=Path, required=True)
    result.add_argument("--module-prefix", required=True)
    result.add_argument("--namespace", required=True)
    result.add_argument("--chunk-size", type=int,
                        choices=range(1, MAX_CHUNK_SIZE + 1),
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
