#!/usr/bin/env python3
"""Emit small benchmarks for the corner-free rounded point-cached leaves.

This is an engineering harness, not a proof-producing generator.  It selects
the first authenticated patched leaf and the accepted refined terminal with
the smallest archived exact lower margin, reconstructs their endpoint point
graphs, and emits independent Lean modules for:

* the rounded point query workload;
* the analytic payload check;
* the rounded-node positivity check;
* the final midpoint evaluation check; and
* the combined corner-free leaf check.

The point values in the checking modules are deliberately computed with
``roundedFastAutoValues``.  Thus these modules benchmark the conservative
all-inline path.  Production cache modules replace selected point definitions
by imported, kernel-checked literals and should only be faster.  Every output
is created exclusively; the script never overwrites an existing artifact.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import re
import sys
from typing import Iterable


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
DEFAULT_REPLAY_MANIFEST = (
    REPOSITORY
    / ".lake/scratch/GeneratedUpperKHistoricalPatchedCachedReplayV1/"
    "AgentUpperKHistoricalPatchedCachedReplayGeneratedManifest.json"
)

# This record is the minimum among all accepted TERMINAL records in the
# archived complete exact-refinement reports.  The patched replay manifest is
# still checked below, so path or box drift fails closed.
TIGHT_ROOT = "oneToTwo"
TIGHT_PATH = "s1k1s1h0k1h0s1h0s0k0h1"
TIGHT_ARCHIVED_LOWER_NANOUNITS = 37_332_696

POINT_BITS = 40
SCALAR_AND_NODE_BITS = 24
TERMS = 12
SQRT_BITS = 40
SQRT_FUEL = 40
LOG_FUEL = 48

PREFIX_RE = re.compile(r"Agent[A-Za-z0-9]+\Z")
PATH_RE = re.compile(r"(?:[skh][01])+\Z")
MAX_MANIFEST_BYTES = 64 * 1024 * 1024


class BenchmarkError(RuntimeError):
    """An input or requested output failed a benchmark guard."""


def fail(message: str) -> None:
    raise BenchmarkError(message)


def q(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def q_typed(value: Fraction) -> str:
    return f"({q(value)} : ℚ)"


def parse_fraction(value: object, context: str) -> Fraction:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a nonempty rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise BenchmarkError(f"invalid rational at {context}: {value!r}") from error
    return result


@dataclass(frozen=True, slots=True)
class Box:
    s_lo: Fraction
    s_hi: Fraction
    k_lo: Fraction
    k_hi: Fraction
    h_lo: Fraction
    h_hi: Fraction

    def center(self) -> "Box":
        s = (self.s_lo + self.s_hi) / 2
        k = (self.k_lo + self.k_hi) / 2
        h = (self.h_lo + self.h_hi) / 2
        return Box(s, s, k, k, h, h)

    def e_bounds(self) -> tuple[Fraction, Fraction]:
        return self.s_lo * self.s_lo * self.k_lo, self.s_hi * self.s_hi * self.k_hi

    def y0_bounds(self) -> tuple[Fraction, Fraction]:
        e_lo, e_hi = self.e_bounds()
        return e_lo * self.h_lo * self.h_lo, e_hi * self.h_hi * self.h_hi


@dataclass(frozen=True, slots=True)
class Selection:
    label: str
    root: str
    root_lean: str
    index: int
    path: str
    box: Box
    source_module: str
    archived_lower_nanounits: int | None


@dataclass(frozen=True, slots=True)
class Endpoint:
    name: str
    kind: str
    s: Fraction
    y: Fraction

    def points(self) -> tuple[Fraction, ...]:
        if self.y == 0:
            return ()
        b = self.s + (1 - self.s) * self.y
        if self.kind == "a":
            return b, self.s
        if self.kind == "c":
            return b, self.y, self.s
        fail(f"internal endpoint kind drift: {self.kind!r}")


def endpoints(box: Box) -> tuple[Endpoint, ...]:
    e_lo, e_hi = box.e_bounds()
    y_lo, y_hi = box.y0_bounds()
    return (
        Endpoint("aY0Lower", "a", box.s_hi, y_lo),
        Endpoint("aY0Upper", "a", box.s_lo, y_hi),
        Endpoint("cY0Lower", "c", box.s_hi, y_hi),
        Endpoint("cY0Upper", "c", box.s_lo, y_lo),
        Endpoint("aELower", "a", box.s_hi, e_lo),
        Endpoint("aEUpper", "a", box.s_lo, e_hi),
        Endpoint("cELower", "c", box.s_hi, e_hi),
        Endpoint("cEUpper", "c", box.s_lo, e_lo),
    )


def read_manifest(path: Path) -> dict[str, object]:
    if path.is_symlink() or not path.is_file():
        fail(f"replay manifest must be a regular nonsymlink file: {path}")
    if path.stat().st_size > MAX_MANIFEST_BYTES:
        fail("replay manifest exceeds the byte guard")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkError(f"could not read replay manifest: {error}") from error
    if not isinstance(value, dict):
        fail("replay manifest must contain a JSON object")
    if value.get("totalLeaves") != 15_398:
        fail("replay manifest does not have the authenticated 15,398 leaves")
    return value


def parse_chunk(label: str, root: dict[str, object], chunk: dict[str, object],
                archived_lower: int | None) -> Selection:
    path = chunk.get("path")
    if not isinstance(path, str) or PATH_RE.fullmatch(path) is None:
        fail(f"invalid {label} path in replay manifest")
    bounds = chunk.get("bounds")
    if not isinstance(bounds, dict):
        fail(f"missing {label} bounds in replay manifest")
    box = Box(
        parse_fraction(bounds.get("sLo"), f"{label}.sLo"),
        parse_fraction(bounds.get("sHi"), f"{label}.sHi"),
        parse_fraction(bounds.get("kLo"), f"{label}.kLo"),
        parse_fraction(bounds.get("kHi"), f"{label}.kHi"),
        parse_fraction(bounds.get("hLo"), f"{label}.hLo"),
        parse_fraction(bounds.get("hHi"), f"{label}.hHi"),
    )
    if not (0 < box.s_lo <= box.s_hi <= Fraction(1, 16)):
        fail(f"{label} escaped the upper-K s range")
    if not (0 < box.k_lo <= box.k_hi <= 4):
        fail(f"{label} escaped the upper-K K range")
    if not (0 <= box.h_lo <= box.h_hi <= 1):
        fail(f"{label} escaped the upper-K chi range")
    index = chunk.get("index")
    module = chunk.get("module")
    root_lean = root.get("rootLean")
    root_key = root.get("key")
    if type(index) is not int or index < 0:
        fail(f"invalid {label} leaf index")
    if not isinstance(module, str) or not module:
        fail(f"invalid {label} source module")
    if not isinstance(root_lean, str) or not root_lean.startswith("Auto."):
        fail(f"invalid {label} root Lean name")
    if not isinstance(root_key, str) or not root_key:
        fail(f"invalid {label} root key")
    return Selection(
        label, root_key, root_lean, index, path, box, module, archived_lower
    )


def selections(manifest: dict[str, object]) -> tuple[Selection, Selection]:
    roots = manifest.get("roots")
    if not isinstance(roots, list) or len(roots) != 2:
        fail("replay manifest must have exactly two roots")
    by_key: dict[str, dict[str, object]] = {}
    for raw_root in roots:
        if not isinstance(raw_root, dict) or not isinstance(raw_root.get("key"), str):
            fail("invalid replay root record")
        by_key[raw_root["key"]] = raw_root
    if set(by_key) != {"oneToTwo", "twoToFour"}:
        fail("unexpected replay root keys")

    ordinary_root = by_key["oneToTwo"]
    ordinary_chunks = ordinary_root.get("chunks")
    if not isinstance(ordinary_chunks, list) or not ordinary_chunks:
        fail("oneToTwo replay has no leaves")
    ordinary_raw = ordinary_chunks[0]
    if not isinstance(ordinary_raw, dict) or ordinary_raw.get("index") != 0:
        fail("first oneToTwo replay leaf drifted")
    ordinary = parse_chunk("ordinary", ordinary_root, ordinary_raw, None)

    tight_root = by_key[TIGHT_ROOT]
    tight_chunks = tight_root.get("chunks")
    if not isinstance(tight_chunks, list):
        fail("tight replay root has no chunk list")
    matches = [
        chunk for chunk in tight_chunks
        if isinstance(chunk, dict) and chunk.get("path") == TIGHT_PATH
    ]
    if len(matches) != 1:
        fail("archived minimum-terminal path is not a unique patched leaf")
    tight = parse_chunk(
        "tight", tight_root, matches[0], TIGHT_ARCHIVED_LOWER_NANOUNITS
    )
    return ordinary, tight


def path_lean(path: str) -> str:
    axes = {"s": ".s", "k": ".k", "h": ".chi"}
    branches = {"0": ".lower", "1": ".upper"}
    steps = []
    for offset in range(0, len(path), 2):
        axis, branch = path[offset], path[offset + 1]
        steps.append(f"{{ axis := {axes[axis]}, branch := {branches[branch]} }}")
    return "[" + ",\n    ".join(steps) + "]"


def box_lean(box: Box) -> str:
    return (
        "{ sLo := " + q(box.s_lo) + ", sHi := " + q(box.s_hi)
        + ", kLo := " + q(box.k_lo) + ", kHi := " + q(box.k_hi)
        + ", chiLo := " + q(box.h_lo) + ", chiHi := " + q(box.h_hi) + " }"
    )


def argument_lean(name: str, endpoint_values: tuple[Endpoint, ...]) -> str:
    fields = []
    for endpoint in endpoint_values:
        fields.append(
            f"    {endpoint.name}S := {q(endpoint.s)}, "
            f"{endpoint.name}Y := {q(endpoint.y)}"
        )
    return (
        f"def {name} : LRUpperKPointEndpointAssembly.Arguments :=\n"
        "  {\n" + "\n".join(fields) + " }\n"
    )


def first_use_points(*endpoint_groups: tuple[Endpoint, ...]) -> list[Fraction]:
    result: list[Fraction] = []
    seen: set[Fraction] = set()
    for group in endpoint_groups:
        for endpoint in group:
            for point in endpoint.points():
                if point not in seen:
                    seen.add(point)
                    result.append(point)
    return result


def endpoint_point_values_lean(
    name: str,
    endpoint_values: tuple[Endpoint, ...],
    point_names: dict[Fraction, str],
) -> str:
    fields = []
    for endpoint in endpoint_values:
        points = endpoint.points()
        if not points:
            value = ".zero"
        else:
            refs = " ".join(point_names[point] for point in points)
            value = f".ofPoints {refs}"
        fields.append(f"    {endpoint.name} := {value}")
    return (
        f"def {name} : LRUpperKPointEndpointAssembly.EndpointPointValues :=\n"
        "  {\n" + "\n".join(fields) + " }\n"
    )


def module_names(prefix: str, selection: Selection) -> dict[str, str]:
    stem = prefix + ("Ordinary" if selection.label == "ordinary" else "Tight")
    return {
        "data": stem + "Data",
        "query": stem + "PointQuery",
        "analytic": stem + "Analytic",
        "nodes": stem + "Nodes",
        "evaluation": stem + "Evaluation",
        "combined": stem + "Combined",
    }


def render_data(prefix: str, selection: Selection) -> tuple[str, str, int]:
    modules = module_names(prefix, selection)
    module = modules["data"]
    namespace = f"CourtadeKumar.{module}"
    center_endpoints = endpoints(selection.box.center())
    whole_endpoints = endpoints(selection.box)
    points = first_use_points(center_endpoints, whole_endpoints)
    point_names = {point: f"pointP{index:04d}" for index, point in enumerate(points)}
    point_defs = "\n".join(
        f"def {point_names[point]} : LRUpperKPointCache.Values :=\n"
        "  LRUpperKPointCache.roundedFastAutoValues\n"
        f"    pointBits terms pointSqrtBits logFuel {q_typed(point)}\n"
        for point in points
    )
    source = "\n".join(
        [
            "import InformationTheory.CourtadeKumar."
            "LRDeterminantUpperKCornerFreePointCachedLeafCertificate",
            "import InformationTheory.CourtadeKumar."
            "LRDeterminantUpperKPointEndpointAssembly",
            "",
            "/-! Generated all-inline data for a corner-free leaf benchmark. -/",
            "",
            f"namespace {namespace}",
            "",
            "open LRUpperKHistoricalPackedCertificate",
            "",
            f"def pointBits : ℕ := {POINT_BITS}",
            f"def dyadicBits : ℕ := {SCALAR_AND_NODE_BITS}",
            f"def terms : ℕ := {TERMS}",
            f"def pointSqrtBits : ℕ := {SQRT_BITS}",
            f"def sqrtFuel : ℕ := {SQRT_FUEL}",
            f"def logFuel : ℕ := {LOG_FUEL}",
            "",
            "def path : Path :=",
            "  " + path_lean(selection.path).replace("\n", "\n  "),
            "",
            "def box : CertificateBox :=",
            "  " + box_lean(selection.box),
            "",
            "set_option maxRecDepth 1000000 in",
            "set_option maxHeartbeats 0 in",
            "theorem box_eq_follow : box = follow "
            f"{selection.root_lean} path := by",
            "  rfl'",
            "",
            "def centerBox : CertificateBox :=",
            "  LRUpperKHistoricalThreeCoordinateBase.centerBox box",
            "",
            argument_lean("centerArguments", center_endpoints).rstrip(),
            "",
            argument_lean("wholeArguments", whole_endpoints).rstrip(),
            "",
            point_defs.rstrip(),
            "",
            endpoint_point_values_lean(
                "centerPointValues", center_endpoints, point_names
            ).rstrip(),
            "",
            endpoint_point_values_lean(
                "wholePointValues", whole_endpoints, point_names
            ).rstrip(),
            "",
            "def centerValues :",
            "    LRUpperKDirectCornerFreePointCachedLeafCertificate.ScalarValues :=",
            "  centerPointValues.scalarValues dyadicBits centerArguments",
            "",
            "def wholeValues :",
            "    LRUpperKDirectCornerFreePointCachedLeafCertificate.ScalarValues :=",
            "  wholePointValues.scalarValues dyadicBits wholeArguments",
            "",
            f"end {namespace}",
            "",
        ]
    )
    return module, source, len(points)


def render_query(prefix: str, selection: Selection) -> tuple[str, str]:
    modules = module_names(prefix, selection)
    module = modules["query"]
    namespace = f"CourtadeKumar.{module}"
    points = first_use_points(endpoints(selection.box.center()), endpoints(selection.box))
    requests = ",\n    ".join(q_typed(point) for point in points)
    source = "\n".join(
        [
            "import InformationTheory.CourtadeKumar.LRDeterminantUpperKPointCache",
            "",
            "/-! Runtime-only query benchmark; its output has no proof authority. -/",
            "",
            f"namespace {namespace}",
            "",
            "def points : List ℚ :=",
            f"  [{requests}]",
            "",
            "def row (z : ℚ) : String :=",
            "  let values := LRUpperKPointCache.roundedFastAutoValues",
            f"    {POINT_BITS} {TERMS} {SQRT_BITS} {LOG_FUEL} z",
            "  String.intercalate \"\\t\"",
            "    [reprStr z, reprStr values.q.lower, reprStr values.q.upper,",
            "      reprStr values.qPrime.lower, reprStr values.qPrime.upper]",
            "",
            "set_option maxRecDepth 1000000 in",
            "#eval points.forM fun z => IO.println (row z)",
            "",
            f"end {namespace}",
            "",
        ]
    )
    return module, source


def render_check(prefix: str, selection: Selection, phase: str) -> tuple[str, str]:
    modules = module_names(prefix, selection)
    module = modules[phase]
    data_module = modules["data"]
    namespace = f"CourtadeKumar.{module}"
    data = f"CourtadeKumar.{data_module}"
    if phase == "analytic":
        proposition = (
            "LRUpperKDirectCornerFreePointCachedLeafCertificate.analyticCheck\n"
            f"      {data}.terms {data}.sqrtFuel {data}.logFuel\n"
            f"      {data}.box = true"
        )
    elif phase == "nodes":
        proposition = (
            "LRUpperKDirectCornerFreePointCachedLeafCertificate.nodeCheck\n"
            f"      {data}.dyadicBits {data}.terms {data}.sqrtFuel {data}.logFuel\n"
            f"      {data}.box {data}.centerValues {data}.wholeValues = true"
        )
    elif phase == "evaluation":
        proposition = (
            "LRUpperKDirectCornerFreePointCachedLeafCertificate.evaluationCheck\n"
            f"      {data}.dyadicBits {data}.terms {data}.sqrtFuel {data}.logFuel\n"
            f"      {data}.box {data}.centerValues {data}.wholeValues = true"
        )
    elif phase == "combined":
        proposition = (
            "LRUpperKDirectCornerFreePointCachedLeafCertificate.check\n"
            f"      {data}.dyadicBits {data}.terms {data}.sqrtFuel {data}.logFuel\n"
            f"      {data}.box {data}.centerValues {data}.wholeValues = true"
        )
    else:
        fail(f"internal benchmark phase drift: {phase!r}")
    source = "\n".join(
        [
            f"import {data_module}",
            "",
            f"namespace {namespace}",
            "",
            "set_option trace.profiler true in",
            "set_option maxRecDepth 1000000 in",
            "set_option maxHeartbeats 0 in",
            "theorem checked :",
            "    " + proposition.replace("\n", "\n  ") + " := by",
            "  rfl'",
            "",
            f"end {namespace}",
            "",
        ]
    )
    return module, source


def build(prefix: str, manifest: dict[str, object]) -> tuple[dict[str, str], dict[str, object]]:
    if PREFIX_RE.fullmatch(prefix) is None or len(prefix) > 72:
        fail("--module-prefix must be an Agent-prefixed ASCII Lean identifier")
    sources: dict[str, str] = {}
    records = []
    for selection in selections(manifest):
        data_module, data_source, point_count = render_data(prefix, selection)
        query_module, query_source = render_query(prefix, selection)
        sources[data_module] = data_source
        sources[query_module] = query_source
        for phase in ("analytic", "nodes", "evaluation", "combined"):
            module, source = render_check(prefix, selection, phase)
            sources[module] = source
        records.append(
            {
                "label": selection.label,
                "root": selection.root,
                "index": selection.index,
                "path": selection.path,
                "bounds": {
                    "sLo": q(selection.box.s_lo),
                    "sHi": q(selection.box.s_hi),
                    "kLo": q(selection.box.k_lo),
                    "kHi": q(selection.box.k_hi),
                    "chiLo": q(selection.box.h_lo),
                    "chiHi": q(selection.box.h_hi),
                },
                "uniquePositivePoints": point_count,
                "archivedExactLowerNanounits": selection.archived_lower_nanounits,
                "sourceReplayModule": selection.source_module,
                "modules": module_names(prefix, selection),
            }
        )
    if len(sources) != 12:
        fail("benchmark source count drifted")
    for module, source in sources.items():
        if source.count("native_decide") or source.count("vm_decide"):
            fail(f"forbidden proof shortcut in generated source {module}")
    plan = {
        "status": "validated-read-only",
        "proofAuthority": "none: timing harness only",
        "parameters": {
            "pointBits": POINT_BITS,
            "scalarAndNodeBits": SCALAR_AND_NODE_BITS,
            "terms": TERMS,
            "pointSqrtBits": SQRT_BITS,
            "sharpSqrtFuel": SQRT_FUEL,
            "logFuel": LOG_FUEL,
            "pointStrategy": "all-inline roundedFastAutoValues",
        },
        "selections": records,
        "outputModules": sorted(sources),
    }
    return sources, plan


def output_directory(raw: str) -> Path:
    supplied = Path(raw)
    try:
        result = supplied.resolve(strict=True)
    except FileNotFoundError as error:
        raise BenchmarkError(f"output directory does not exist: {supplied}") from error
    scratch = (REPOSITORY / ".lake/scratch").resolve(strict=True)
    if result != scratch or not result.is_dir() or result.is_symlink():
        fail("output directory must be the existing repository-local .lake/scratch")
    return result


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "command", choices=("plan", "generate"),
        help="validate only, or exclusively emit the twelve scratch modules",
    )
    result.add_argument(
        "--manifest", default=str(DEFAULT_REPLAY_MANIFEST),
        help="existing scalar-cached replay manifest used only as a leaf index",
    )
    result.add_argument(
        "--module-prefix", default="AgentUpperKCornerFreeLeafBenchmark",
    )
    result.add_argument("--output-dir", default=str(REPOSITORY / ".lake/scratch"))
    result.add_argument("--confirm-write", action="store_true")
    return result


def main(argv: Iterable[str] | None = None) -> None:
    args = parser().parse_args(list(argv) if argv is not None else None)
    manifest_path = Path(args.manifest).resolve(strict=True)
    manifest = read_manifest(manifest_path)
    sources, plan = build(args.module_prefix, manifest)
    if args.command == "plan":
        print(json.dumps(plan, indent=2, sort_keys=True))
        return
    if not args.confirm_write:
        fail("refusing benchmark emission without --confirm-write")
    directory = output_directory(args.output_dir)
    paths = {directory / f"{module}.lean": source for module, source in sources.items()}
    collisions = sorted(path.name for path in paths if path.exists() or path.is_symlink())
    if collisions:
        fail(f"refusing to overwrite benchmark artifacts: {collisions}")
    created: list[Path] = []
    try:
        for path, source in paths.items():
            with path.open("x", encoding="utf-8", newline="\n") as handle:
                handle.write(source)
            created.append(path)
    except Exception:
        for path in created:
            path.unlink(missing_ok=True)
        raise
    result = dict(plan)
    result["status"] = "written"
    result["writtenFiles"] = len(created)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (BenchmarkError, FileNotFoundError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
