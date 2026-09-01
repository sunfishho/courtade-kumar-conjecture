#!/usr/bin/env python3
"""Generate one-kernel-terminal-per-module compact-V replay sources.

The input plan is emitted by Lean's exact staged selector, but remains
untrusted.  This script validates its complete binary topology and literal
boxes before emitting sources.  Every terminal is then independently checked
by Lean's ordinary kernel; structural assembly contains no certificate
arithmetic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import TypeAlias


class GenerationError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise GenerationError(message)


RATIONAL_RE = re.compile(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?")
PATH_RE = re.compile(r"r[LR]*")
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9]*(?:\.[A-Z][A-Za-z0-9]*)+")
NAMESPACE_RE = re.compile(r"[A-Z][A-Za-z0-9]*")


def parse_nat(text: str, context: str) -> int:
    if not re.fullmatch(r"0|[1-9][0-9]*", text):
        fail(f"{context}: expected canonical natural, got {text!r}")
    return int(text)


def parse_int(text: str, context: str) -> int:
    if not re.fullmatch(r"-?(?:0|[1-9][0-9]*)", text) or text == "-0":
        fail(f"{context}: expected canonical integer, got {text!r}")
    return int(text)


def parse_rat(text: str, context: str) -> Fraction:
    if not RATIONAL_RE.fullmatch(text):
        fail(f"{context}: malformed rational {text!r}")
    value = Fraction(text)
    if str(value) != text:
        fail(f"{context}: noncanonical rational {text!r}; expected {value}")
    return value


@dataclass(frozen=True)
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
        return Box(self.s_lo, self.s_hi, self.k_lo, self.k_hi,
                   self.chi_lo, cut)

    def upper(self, axis: str, cut: Fraction) -> "Box":
        if axis == "s":
            return Box(cut, self.s_hi, self.k_lo, self.k_hi,
                       self.chi_lo, self.chi_hi)
        if axis == "k":
            return Box(self.s_lo, self.s_hi, cut, self.k_hi,
                       self.chi_lo, self.chi_hi)
        return Box(self.s_lo, self.s_hi, self.k_lo, self.k_hi,
                   cut, self.chi_hi)

    def bounds(self, axis: str) -> tuple[Fraction, Fraction]:
        if axis == "s":
            return self.s_lo, self.s_hi
        if axis == "k":
            return self.k_lo, self.k_hi
        return self.chi_lo, self.chi_hi


@dataclass(frozen=True)
class LogRange:
    exponent: int
    mantissa: Fraction


@dataclass(frozen=True)
class LogInterval:
    lower: LogRange
    upper: LogRange


@dataclass(frozen=True)
class BPayload:
    log_one_plus_v: LogInterval
    log_one_sub_ry: LogInterval


@dataclass(frozen=True)
class Split:
    path: str
    axis: str
    cut: Fraction


@dataclass(frozen=True)
class Accept:
    index: int
    path: str
    kind: str
    head: str
    box: Box
    same_y_log: LogRange | None
    b: BPayload | None


@dataclass(frozen=True)
class Discard:
    index: int
    path: str
    box: Box
    b: BPayload
    log_one_sub_y: LogInterval


Node: TypeAlias = Split | Accept | Discard


@dataclass(frozen=True)
class Plan:
    parameters: tuple[int, int, int, int, int, int, int]
    root: Box
    nodes: dict[str, Node]
    boxes: dict[str, Box]
    terminals: tuple[Accept | Discard, ...]
    source_sha256: str


def parse_box(fields: list[str], context: str) -> Box:
    if len(fields) != 6:
        fail(f"{context}: expected six box endpoints")
    values = [parse_rat(value, f"{context} endpoint {index}")
              for index, value in enumerate(fields)]
    box = Box(*values)
    if not (box.s_lo <= box.s_hi and box.k_lo <= box.k_hi
            and box.chi_lo <= box.chi_hi):
        fail(f"{context}: inverted box")
    return box


def parse_log_range(fields: list[str], context: str) -> LogRange:
    if len(fields) != 2:
        fail(f"{context}: expected exponent and mantissa")
    return LogRange(parse_int(fields[0], f"{context} exponent"),
                    parse_rat(fields[1], f"{context} mantissa"))


def parse_log_interval(fields: list[str], context: str) -> LogInterval:
    if len(fields) != 4:
        fail(f"{context}: expected four logarithm fields")
    return LogInterval(parse_log_range(fields[:2], f"{context} lower"),
                       parse_log_range(fields[2:], f"{context} upper"))


def parse_b(fields: list[str], context: str) -> BPayload:
    if len(fields) != 8:
        fail(f"{context}: expected eight B-certificate fields")
    return BPayload(parse_log_interval(fields[:4], f"{context} log(1+v)"),
                    parse_log_interval(fields[4:], f"{context} log(1-Ry)"))


def validate_path(path: str, context: str) -> None:
    if not PATH_RE.fullmatch(path):
        fail(f"{context}: invalid binary path {path!r}")


def parse_plan(path: Path) -> Plan:
    raw = path.read_bytes()
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        fail(f"plan is not ASCII: {error}")
    lines = text.splitlines()
    if not lines:
        fail("empty plan")
    header = lines[0].split("\t")
    if len(header) != 15 or header[:2] != ["H", "compact-v-staged-plan-v1"]:
        fail("invalid plan header")
    parameters = tuple(parse_nat(value, f"header parameter {index}")
                       for index, value in enumerate(header[2:9]))
    root = parse_box(header[9:], "root")
    nodes: dict[str, Node] = {}
    terminals: list[Accept | Discard] = []
    footer_count: int | None = None
    for line_number, line in enumerate(lines[1:], start=2):
        fields = line.split("\t")
        context = f"line {line_number}"
        if footer_count is not None:
            fail(f"{context}: data after footer")
        if fields[0] == "E":
            if len(fields) != 2:
                fail(f"{context}: malformed footer")
            footer_count = parse_nat(fields[1], f"{context} count")
            continue
        if fields[0] == "F":
            fail(f"{context}: unresolved frontier; refusing certificate emission")
        if fields[0] == "N":
            if len(fields) != 4:
                fail(f"{context}: malformed split")
            node_path, axis = fields[1], fields[2]
            validate_path(node_path, context)
            if axis not in {"s", "k", "chi"}:
                fail(f"{context}: invalid axis {axis!r}")
            node: Node = Split(node_path, axis,
                               parse_rat(fields[3], f"{context} cut"))
        elif fields[0] == "A":
            if len(fields) < 11:
                fail(f"{context}: truncated accepted terminal")
            index = parse_nat(fields[1], f"{context} index")
            node_path, kind, head = fields[2:5]
            validate_path(node_path, context)
            box = parse_box(fields[5:11], f"{context} box")
            if kind == "sameY":
                if head not in {"n128", "n192"} or len(fields) != 13:
                    fail(f"{context}: malformed same-y terminal")
                node = Accept(index, node_path, kind, head, box,
                              parse_log_range(fields[11:], context), None)
            elif kind == "independent":
                if head not in {"n128", "n192"} or len(fields) != 19:
                    fail(f"{context}: malformed independent terminal")
                node = Accept(index, node_path, kind, head, box, None,
                              parse_b(fields[11:], context))
            elif kind == "direct":
                if head != "none" or len(fields) != 19:
                    fail(f"{context}: malformed direct terminal")
                node = Accept(index, node_path, kind, head, box, None,
                              parse_b(fields[11:], context))
            else:
                fail(f"{context}: unknown accepted kind {kind!r}")
            terminals.append(node)
        elif fields[0] == "X":
            if len(fields) != 23 or fields[3:5] != ["discard", "none"]:
                fail(f"{context}: malformed discard terminal")
            index = parse_nat(fields[1], f"{context} index")
            node_path = fields[2]
            validate_path(node_path, context)
            node = Discard(index, node_path,
                           parse_box(fields[5:11], f"{context} box"),
                           parse_b(fields[11:19], f"{context} B"),
                           parse_log_interval(fields[19:23],
                                              f"{context} log(1-y)"))
            terminals.append(node)
        else:
            fail(f"{context}: unknown record tag {fields[0]!r}")
        if node.path in nodes:
            fail(f"{context}: duplicate path {node.path}")
        nodes[node.path] = node
    if footer_count is None:
        fail("missing footer")
    if footer_count != len(terminals):
        fail(f"footer says {footer_count} terminals, parsed {len(terminals)}")
    if [terminal.index for terminal in terminals] != list(range(len(terminals))):
        fail("terminal indices are not contiguous depth-first indices")
    fuel = parameters[-1]
    boxes: dict[str, Box] = {}
    preorder_terminals: list[int] = []
    visited: set[str] = set()

    def visit(node_path: str, expected: Box) -> None:
        if node_path not in nodes:
            fail(f"topology is missing path {node_path}")
        node = nodes[node_path]
        visited.add(node_path)
        boxes[node_path] = expected
        if isinstance(node, Split):
            if len(node_path) - 1 >= fuel:
                fail(f"split {node_path} exceeds configured fuel {fuel}")
            lo, hi = expected.bounds(node.axis)
            if not lo <= node.cut <= hi:
                fail(f"split {node_path} cut lies outside its box")
            visit(node_path + "L", expected.lower(node.axis, node.cut))
            visit(node_path + "R", expected.upper(node.axis, node.cut))
        else:
            if node.box != expected:
                fail(f"terminal {node_path} printed a box inconsistent with its path")
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
                hashlib.sha256(raw).hexdigest())


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def lean_box(name: str, box: Box) -> str:
    return (f"def {name} : CertificateBox where\n"
            f"  sLo := {lean_rat(box.s_lo)}\n"
            f"  sHi := {lean_rat(box.s_hi)}\n"
            f"  kLo := {lean_rat(box.k_lo)}\n"
            f"  kHi := {lean_rat(box.k_hi)}\n"
            f"  chiLo := {lean_rat(box.chi_lo)}\n"
            f"  chiHi := {lean_rat(box.chi_hi)}\n")


def lean_log_range(value: LogRange) -> str:
    return ("{ exponent := " + str(value.exponent)
            + ", mantissa := " + lean_rat(value.mantissa) + " }")


def lean_log_interval(value: LogInterval) -> str:
    return ("{ lower := " + lean_log_range(value.lower)
            + ", upper := " + lean_log_range(value.upper) + " }")


def lean_b(value: BPayload) -> str:
    return ("{ logOnePlusV := " + lean_log_interval(value.log_one_plus_v)
            + ", logOneSubRY := " + lean_log_interval(value.log_one_sub_ry)
            + " }")


def config_source(plan: Plan, namespace: str) -> str:
    names = ["logTerms", "pZeroTerms", "wTerms", "dTerms", "directN",
             "logFuel", "fuel"]
    parameters = "\n".join(
        f"def {name} : ℕ := {value}"
        for name, value in zip(names, plan.parameters, strict=True))
    boxes = "\n".join(
        lean_box("box_" + path, plan.boxes[path])
        for path in sorted(plan.boxes, key=lambda item: (len(item), item)))
    return f"""import InformationTheory.CourtadeKumar.LRCompactVStagedGroupedCheckedTree
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-! Generated from an untrusted exact-Lean plan.  Terminal kernel checks are
the sole arithmetic proof authority.  Plan SHA-256: {plan.source_sha256}. -/

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

abbrev CheckedTree := LRCompactVStagedGroupedCheckedTree.CheckedTree

def planSha256 : String := "{plan.source_sha256}"

{parameters}

{boxes}
abbrev rootBox : CertificateBox := box_r

end {namespace}
end CourtadeKumar
"""


def accept_data(terminal: Accept) -> str:
    if terminal.kind == "sameY":
        assert terminal.same_y_log is not None
        return (".sameY\n    { logOnePlusVHi := "
                + lean_log_range(terminal.same_y_log)
                + f"\n      headChoice := .{terminal.head} }}")
    assert terminal.b is not None
    if terminal.kind == "independent":
        return (".grouped\n    { b := " + lean_b(terminal.b)
                + f"\n      headChoice := .{terminal.head} }}")
    return ".direct\n    { b := " + lean_b(terminal.b) + " }"


def leaf_source(terminal: Accept | Discard, module_prefix: str,
                namespace: str) -> str:
    ordinal = terminal.index
    stem = f"leaf{ordinal:03d}"
    box_name = "box_" + terminal.path
    if isinstance(terminal, Accept):
        data_type = "LRCompactVStagedGroupedLeafCertificate"
        data = accept_data(terminal)
        check = (f"{stem}Data.check logTerms pZeroTerms wTerms dTerms "
                 f"directN {box_name}")
        checked = ("LRCompactVStagedGroupedCheckedTree.ofAccept\n"
                   f"    logTerms pZeroTerms wTerms dTerms directN\n"
                   f"    {stem}Data {stem}Check")
    else:
        data_type = "LRCompactVDiscardCertificate"
        data = ("{ b := " + lean_b(terminal.b)
                + ", logOneSubY := "
                + lean_log_interval(terminal.log_one_sub_y) + " }")
        check = f"{stem}Data.check logTerms {box_name}"
        checked = ("LRCompactVStagedGroupedCheckedTree.ofDiscard\n"
                   f"    logTerms {stem}Data {stem}Check")
    return f"""import {module_prefix}.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

def {stem}Data : {data_type} :=
  {data}

#kernel_checked_bool {stem}Check
  ({check})

def {stem}Checked : CheckedTree {box_name} :=
  {checked}

end {namespace}
end CourtadeKumar
"""


def assembly_source(plan: Plan, module_prefix: str, namespace: str) -> str:
    imports = "\n".join(
        f"import {module_prefix}.Leaf{terminal.index:03d}"
        for terminal in plan.terminals)
    terminal_names = {
        terminal.path: f"leaf{terminal.index:03d}Checked"
        for terminal in plan.terminals
    }
    definitions: list[str] = []
    for path in sorted(
            (path for path, node in plan.nodes.items()
             if isinstance(node, Split)),
            key=lambda item: (-len(item), item)):
        split = plan.nodes[path]
        assert isinstance(split, Split)
        lower_path, upper_path = path + "L", path + "R"
        lower = terminal_names.get(lower_path, "node_" + lower_path)
        upper = terminal_names.get(upper_path, "node_" + upper_path)
        definitions.append(f"""def node_{path} : CheckedTree box_{path} :=
  LRCompactVStagedGroupedCheckedTree.joinLiteral
    box_{path} box_{lower_path} box_{upper_path} .{split.axis}
    {lean_rat(split.cut)} (by rfl) (by rfl) {lower} {upper}
""")
    body = "\n".join(definitions)
    return f"""{imports}

/-! Arithmetic-free assembly of independently kernel-checked terminals. -/

set_option autoImplicit false

namespace CourtadeKumar
namespace {namespace}

{body}
abbrev checkedRoot : CheckedTree rootBox := node_r

theorem sound :
    ∀ point, rootBox.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  checkedRoot.target_nonnegative

end {namespace}
end CourtadeKumar
"""


def atomic_write(path: Path, text: str, force: bool) -> None:
    encoded = text.encode("utf-8")
    if path.exists():
        if path.read_bytes() == encoded:
            return
        if not force:
            fail(f"refusing to replace differing file {path}; pass --force")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".building")
    temporary.write_bytes(encoded)
    os.replace(temporary, path)


def generate(args: argparse.Namespace) -> None:
    plan = parse_plan(args.plan)
    if not MODULE_RE.fullmatch(args.module_prefix):
        fail("--module-prefix must be a dotted Lean module name")
    if not NAMESPACE_RE.fullmatch(args.namespace):
        fail("--namespace must be one Lean namespace identifier")
    output = args.output_dir
    files: dict[str, str] = {"Config.lean": config_source(plan, args.namespace)}
    for terminal in plan.terminals:
        files[f"Leaf{terminal.index:03d}.lean"] = leaf_source(
            terminal, args.module_prefix, args.namespace)
    files["Assembly.lean"] = assembly_source(
        plan, args.module_prefix, args.namespace)
    manifest = {
        "format": "compact-v-segmented-replay-v1",
        "planSha256": plan.source_sha256,
        "parameters": list(plan.parameters),
        "terminalCount": len(plan.terminals),
        "splitCount": sum(isinstance(node, Split)
                          for node in plan.nodes.values()),
        "terminalKinds": {
            kind: sum((isinstance(terminal, Discard) and kind == "discard")
                      or (isinstance(terminal, Accept)
                          and terminal.kind == kind)
                      for terminal in plan.terminals)
            for kind in ("sameY", "independent", "direct", "discard")
        },
        "modulePrefix": args.module_prefix,
        "namespace": args.namespace,
        "files": {
            name: hashlib.sha256(source.encode("utf-8")).hexdigest()
            for name, source in sorted(files.items())
        },
    }
    for name, source in files.items():
        atomic_write(output / name, source, args.force)
    atomic_write(output / "manifest.json",
                 json.dumps(manifest, indent=2, sort_keys=True) + "\n",
                 args.force)
    print(json.dumps({key: manifest[key] for key in (
        "planSha256", "terminalCount", "splitCount", "terminalKinds")},
        sort_keys=True))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("plan", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--module-prefix", required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    try:
        generate(args)
    except (GenerationError, OSError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
