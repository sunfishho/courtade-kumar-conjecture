#!/usr/bin/env python3
"""Plan or emit the authenticated patched upper-``K`` Lean replay.

The hardened bridge receipt, the two patched preorder streams, and every hash
which identifies them are caller supplied.  Before planning any Lean source
this tool independently authenticates the canonical bridge receipt and its
authoritative closure/aggregate commitments, the PatchApplier result manifest,
the bridge-produced patch manifest and failure evidence, the exact newline-
terminated stream bytes, the normalized topology hashes, all parsed
statistics, the evaluator configuration, and the two-stream aggregate.

The replay plan has two deliberately separate parts:

* every authenticated leaf path gets three bounded ordinary-``rfl'`` checks
  for the analytic payloads, rounded nodes, and midpoint evaluator;
* the authenticated topology is rebuilt in height layers with semantic
  ``joinAtPath`` operations.

The structural part never repeats leaf arithmetic.  Import fan-in modules keep
both the generated import lists and structural modules bounded.  The two
historical roots remain separate until the final direct-tree theorem; no
synthetic ``[1,4]`` root is ever created.

``plan`` is read-only.  ``generate`` additionally requires the plan hash from
a prior planning pass and ``--confirm-write``.  Emission uses exclusive file
creation and is confined to a caller-supplied existing directory below the
repository's ``.lake/scratch`` directory.  This program never invokes Lean and
the generated Python plan has no proof authority: the emitted direct checks are
the sole analytic authority.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
from typing import Any, Iterable, Iterator


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()

ALPHABET = frozenset("Mskh")
ROOT_KEYS = ("oneToTwo", "twoToFour")
MAX_INPUT_BYTES = 1 * 1024 * 1024
MAX_MANIFEST_BYTES = 8 * 1024 * 1024
MAX_RECEIPT_BYTES = 8 * 1024 * 1024
MAX_CLOSURE_DESCRIPTION_BYTES = 16 * 1024 * 1024
MAX_TOOL_BYTES = 8 * 1024 * 1024
MAX_JSON_INTEGER_DIGITS = 256
MAX_JSON_NESTING = 64
MAX_JSON_COLLECTION_ITEMS = 50_000
MAX_TOPOLOGY_NODES_PER_ROOT = 100_000
MAX_TOTAL_TOPOLOGY_NODES = 200_000
MAX_TOPOLOGY_DEPTH = 64
MAX_GENERATED_MODULES = 20_000
MAX_GENERATED_SOURCE_BYTES = 256 * 1024 * 1024
PATCH_GUARD_KEYS = {
    "maxPatchesPerRoot",
    "maxExtraDepthPerPatch",
    "maxReplacementNodesPerPatch",
    "maxTotalAddedInternal",
    "maxFinalNodesPerRoot",
    "maxCombinedFinalNodes",
    "maxPatchedDepth",
}
EXPECTED_PATCH_APPLIER_CEILINGS = {
    "maxPatchesPerRoot": 1536,
    "maxExtraDepthPerPatch": 16,
    "maxReplacementNodesPerPatch": 4097,
    "maxTotalAddedInternal": 3023,
    "maxFinalNodesPerRoot": 20_000,
    "maxCombinedFinalNodes": 40_000,
    "maxPatchedDepth": 30,
}

BRIDGE_TOOL = "AgentUpperKHistoricalExactPatchBridge.py"
AGGREGATOR_TOOL = "AgentUpperKHistoricalExactRefinementAggregate.py"
PATCH_APPLIER_TOOL = "AgentUpperKHistoricalPatchApplier.py"
CLOSURE_PROFILE_GENERATOR_TOOL = (
    "AgentUpperKHistoricalAuthoritativeClosureProfile.py"
)
READY_RECEIPT_STATUS = "ready-current-patch-applier-inputs"
RECEIPT_HASH_RULE = (
    "SHA-256 of compact canonical JSON with receiptPayloadSha256 omitted"
)
EXPECTED_EVALUATOR_IDENTITY = "LRUpperKHistoricalConcreteEvaluator.check"
EXPECTED_EVALUATOR_PARAMETERS = {
    "terms": 12,
    "sqrtFuel": 40,
    "logFuel": 48,
    "payloadPolicy": "historical-auto-payload-v1",
    "qSecondPolicy": "sharp-monotone-endpoints-v1",
}
EXPECTED_PROJECT_ENVELOPE_FILES = 412
EXPECTED_PROJECT_ENVELOPE_PATHS_SHA256 = (
    "96b6b5a77076feb75b0327c17475d18d1357df07cc93a11e7c6bc849c6d64c25"
)
EXPECTED_EVALUATOR_PROJECT_FILES = 397
EXPECTED_EVALUATOR_PATHS_SHA256 = (
    "4a32fa6fc13299813bb16912a44f04aa1a175401c7e953bf54ee3bda7a0ccc4e"
)
EXPECTED_AUDIT_LEAN_FILES = 415
EXPECTED_AUDIT_PATHS_SHA256 = (
    "240c05185fc5f05311bddc8cce2089749c19924d02f1e28b6638a0ab7a77b79a"
)
EXPECTED_ENVIRONMENT_FILES = 3
EXPECTED_MATHLIB_BOUNDARY_IMPORTS = 21
EXPECTED_MATHLIB_BOUNDARY_SHA256 = (
    "934cd8efea653a622d5139ef54956143b85f0d6860b8f1a4ffe490357fc704fa"
)
EXPECTED_AUTHENTICATED_REPOSITORY_FILES = 418
EXPECTED_MATHLIB_TREE_ALGORITHM = "mathlib-lean-source-tree-v1"
EXPECTED_MATHLIB_STABILITY_SCANS = 2
EXPECTED_PROFILE_ID = "upper-k-historical-concrete-audit-closure-v1"
EXPECTED_CLOSURE_POLICY = "pinned-upper-k-evaluator-and-audit-closure-v2"
EXPECTED_AUTHORITY_PROFILE_SHA256 = (
    "57af93f6630a38baf548bfb03b2c20b6d17ab0c17b4e310308eab30d68a8acea"
)

BASE_MANIFEST_FILE = "GeneratedUpperKHistorical.manifest.json"
BASE_MANIFEST_BYTE_SHA256 = (
    "07ec3bc8086a9eecfb42c799a125c47bc8c0de3b3929c57415e187223f9f171a"
)
BASE_AGGREGATE_SHA256 = (
    "a71c6fa1087a5e82f7f8691588f5ba9b37f12f66ac6314f2e8b683e984e7b906"
)
PRECISION_BITS = 132
PROOF_AUTHORITY = (
    "ordinary Lean direct-leaf reductions and semantic structural joins; this "
    "generator is untrusted"
)
FINAL_THEOREM = "lrDeterminantUpperKRegion_historicalPatched_proved"
GENERATED_NAMESPACE = "LRUpperKHistoricalPatchedReplayGenerated"
DIRECT_REPLAY_SOURCE_SET_ALGORITHM = "canonical-json-path-byte-sha256-v1"
DIRECT_REPLAY_SOURCE_FILES = (
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKBalancedAuxiliaryChecker.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKBalancedBasePayloadChecker.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKExplicitPayloadSemanticBridge.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKExplicitCornerPayload.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKExplicitCornerEvaluator.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKExplicitEvaluatorNodes.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKMidpointCoarsening.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKDyadicOuterRounding.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKRoundedEvaluatorArithmetic.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKRoundedExplicitCornerEvaluator.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantAutoCertificateCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantAutoQCertificateCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantAutoCompositeCertificateCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantAutoRegularizedScaleCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKAutoBaseCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKAutoSharpCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKAutoCornerCorrectness.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKDirectCheckedTree.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKDirectLeafCertificate.lean",
)

FORBIDDEN_LEAN = (
    "native_decide",
    "vm_decide",
    "run_tac",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
    "unsafe ",
    "partial ",
    "sorry",
    "admit",
    "axiom ",
)


class ReplayPlanError(RuntimeError):
    """A deterministic authentication, planning, or emission failure."""


def fail(message: str) -> None:
    raise ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("ascii"))


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def pretty_json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            fail(f"JSON object contains duplicate key {key!r}")
        result[key] = value
    return result


def reject_json_constant(token: str) -> None:
    fail(f"nonstandard JSON constant is forbidden: {token}")


def reject_json_float(token: str) -> None:
    fail(f"JSON floating-point number is forbidden: {token}")


def bounded_json_int(token: str) -> int:
    digits = token[1:] if token.startswith("-") else token
    if len(digits) > MAX_JSON_INTEGER_DIGITS:
        fail("JSON integer exceeds the digit guard")
    return int(token)


def parse_json(data: bytes, context: str) -> dict[str, Any]:
    try:
        value = json.loads(
            data,
            object_pairs_hook=strict_object,
            parse_constant=reject_json_constant,
            parse_int=bounded_json_int,
            parse_float=reject_json_float,
        )
    except ReplayPlanError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError, RecursionError) as error:
        fail(f"{context} is not strict UTF-8 JSON: {error}")
    if not isinstance(value, dict):
        fail(f"{context} must be a JSON object")
    return value


def require_exact_keys(value: dict[str, Any], expected: set[str], context: str) -> None:
    observed = set(value)
    if observed != expected:
        fail(
            f"{context} key set drifted; missing={sorted(expected - observed)}, "
            f"extra={sorted(observed - expected)}"
        )


def require_dict(value: object, context: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    return value


def require_list(value: object, context: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{context} must be an array")
    return value


def require_int(value: object, context: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{context} must be an integer")
    if minimum is not None and value < minimum:
        fail(f"{context} must be at least {minimum}")
    return value


def require_string(value: object, context: str) -> str:
    if not isinstance(value, str):
        fail(f"{context} must be a string")
    return value


def require_bool(value: object, context: str) -> bool:
    if type(value) is not bool:
        fail(f"{context} must be a JSON Boolean")
    return value


def require_exact_json_value(value: object, expected: object, context: str) -> None:
    """Compare parsed JSON without Python's Boolean/integer aliasing."""
    if type(value) is not type(expected):
        fail(f"{context} has the wrong JSON type")
    if isinstance(expected, dict):
        observed = require_dict(value, context)
        require_exact_keys(observed, set(expected), context)
        for key, expected_child in expected.items():
            require_exact_json_value(
                observed[key], expected_child, f"{context}.{key}"
            )
        return
    if isinstance(expected, list):
        observed_list = require_list(value, context)
        if len(observed_list) != len(expected):
            fail(f"{context} has the wrong array length")
        for index, (child, expected_child) in enumerate(
            zip(observed_list, expected, strict=True)
        ):
            require_exact_json_value(child, expected_child, f"{context}[{index}]")
        return
    if value != expected:
        fail(f"{context} differs from the authenticated value")


HEX64 = re.compile(r"[0-9a-f]{64}")
SAFE_FILENAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")


def require_hex64(value: object, context: str) -> str:
    text = require_string(value, context)
    if HEX64.fullmatch(text) is None:
        fail(f"{context} must be a lowercase SHA-256 hex digest")
    return text


def supplied_hex64(value: str, option: str) -> str:
    if HEX64.fullmatch(value) is None:
        fail(f"{option} must be a lowercase SHA-256 hex digest")
    return value


def validate_bare_filename(value: object, context: str, suffix: str) -> str:
    result = require_string(value, context)
    candidate = Path(result)
    if (
        candidate.is_absolute()
        or candidate.name != result
        or result in (".", "..")
        or len(result) > 200
        or SAFE_FILENAME.fullmatch(result) is None
        or not result.endswith(suffix)
    ):
        fail(f"{context} must be a bare safe filename ending in {suffix}")
    return result


def direct_scratch_input(raw: str, context: str, suffix: str) -> Path:
    candidate = Path(raw)
    if not candidate.is_absolute():
        candidate = REPOSITORY / candidate
    candidate = Path(os.path.abspath(candidate))
    name = validate_bare_filename(candidate.name, context, suffix)
    if candidate.parent != SCRATCH or candidate.name != name:
        fail(f"{context} must name a direct repository .lake/scratch artifact")
    return candidate


def direct_scratch_reference(value: object, context: str, suffix: str) -> Path:
    name = validate_bare_filename(value, context, suffix)
    return SCRATCH / name


def require_canonical_json_file(
    data: bytes, value: dict[str, Any], context: str
) -> None:
    if data != canonical_json_bytes(value) + b"\n":
        fail(f"{context} must be compact canonical JSON followed by exactly one LF")


def validate_repository_location() -> None:
    if SCRATCH.name != "scratch" or SCRATCH.parent.name != ".lake":
        fail("repository-local scratch directory has an unexpected location")
    expected_scratch = (REPOSITORY / ".lake" / "scratch").resolve()
    if SCRATCH != expected_scratch:
        fail("scratch directory does not equal the repository .lake/scratch path")
    if SCRIPT.parent != (REPOSITORY / "scripts").resolve():
        fail("generator must be installed in the repository scripts directory")
    if not (REPOSITORY / "lakefile.toml").is_file():
        fail("repository marker lakefile.toml is missing")
    if not (REPOSITORY / "InformationTheory").is_dir():
        fail("repository marker InformationTheory/ is missing")


def project_path(raw: str, context: str) -> Path:
    candidate = Path(raw)
    if not candidate.is_absolute():
        candidate = REPOSITORY / candidate
    try:
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError) as error:
        fail(f"{context} does not resolve to an existing path: {error}")
    try:
        resolved.relative_to(REPOSITORY)
    except ValueError:
        fail(f"{context} escaped the writable repository: {resolved}")
    return resolved


def relative_project_path(path: Path) -> str:
    return path.relative_to(REPOSITORY).as_posix()


def read_regular_file(path: Path, context: str, maximum: int) -> bytes:
    try:
        supplied_metadata = path.lstat()
    except OSError as error:
        fail(f"cannot inspect {context}: {error}")
    if stat.S_ISLNK(supplied_metadata.st_mode):
        fail(f"{context} may not be a symbolic link")
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        fail(f"cannot open {context}: {error}")
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            fail(f"{context} must be a regular file")
        if before.st_size > maximum:
            fail(f"{context} exceeds the {maximum}-byte guard")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            block = os.read(descriptor, min(remaining, 1024 * 1024))
            if not block:
                fail(f"{context} changed while being read")
            chunks.append(block)
            remaining -= len(block)
        if os.read(descriptor, 1):
            fail(f"{context} grew while being read")
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    identity_before = (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
    )
    identity_after = (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    )
    if identity_before != identity_after:
        fail(f"{context} changed while being authenticated")
    return b"".join(chunks)


def bind_direct_replay_sources() -> dict[str, object]:
    """Bind the replay plan to the exact post-audit Lean implementation."""
    records: list[dict[str, object]] = []
    for relative in DIRECT_REPLAY_SOURCE_FILES:
        path = project_path(relative, f"direct replay source {relative}")
        data = read_regular_file(path, f"direct replay source {relative}", MAX_INPUT_BYTES)
        records.append(
            {
                "file": relative,
                "bytes": len(data),
                "byteSha256": sha256_bytes(data),
            }
        )
    core: dict[str, object] = {
        "algorithm": DIRECT_REPLAY_SOURCE_SET_ALGORITHM,
        "files": records,
    }
    return {**core, "sourceSetSha256": sha256_bytes(canonical_json_bytes(core))}


def output_directory(raw: str) -> tuple[Path, tuple[int, int]]:
    directory = project_path(raw, "--output-dir")
    try:
        directory.relative_to(SCRATCH)
    except ValueError:
        fail("--output-dir must be inside the repository .lake/scratch directory")
    if directory == SCRATCH:
        fail("--output-dir must be a dedicated child of .lake/scratch")
    metadata = directory.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        fail("--output-dir must be a real existing directory, not a symlink")
    return directory, (metadata.st_dev, metadata.st_ino)


def safe_output_path(directory: Path, filename: str) -> Path:
    if Path(filename).name != filename or not filename.isascii():
        fail(f"invalid generated filename {filename!r}")
    candidate = directory / filename
    if candidate.parent != directory:
        fail(f"generated output escaped --output-dir: {candidate}")
    return candidate


@dataclass(frozen=True, slots=True)
class Step:
    axis: str
    branch: int


PathSteps = tuple[Step, ...]


@dataclass(frozen=True, slots=True)
class Node:
    token: str
    lower: "Node | None" = None
    upper: "Node | None" = None

    @property
    def is_leaf(self) -> bool:
        return self.token == "M"

    def packed(self) -> str:
        if self.is_leaf:
            return "M"
        assert self.lower is not None and self.upper is not None
        return self.token + self.lower.packed() + self.upper.packed()


@dataclass(frozen=True, slots=True)
class Stats:
    nodes: int
    internal: int
    leaves: int
    max_depth: int
    split_s: int
    split_k: int
    split_h: int

    def output_record(self, topology: str, file_bytes: bytes) -> dict[str, object]:
        return {
            "nodes": self.nodes,
            "internal": self.internal,
            "leaves": self.leaves,
            "maxDepth": self.max_depth,
            "topologyBytes": len(topology),
            "topologySha256": sha256_text(topology),
            "byteSha256": sha256_bytes(file_bytes),
        }


class TopologyParser:
    def __init__(self, topology: str):
        self.topology = topology
        self.cursor = 0
        self.nodes = 0
        self.internal = 0
        self.leaves = 0
        self.split_s = 0
        self.split_k = 0
        self.split_h = 0
        self.maximum_depth = 0

    def parse(self, depth: int = 0) -> Node:
        if depth > MAX_TOPOLOGY_DEPTH:
            fail(f"topology exceeded depth guard {MAX_TOPOLOGY_DEPTH}")
        if self.cursor >= len(self.topology):
            fail("truncated preorder topology")
        token = self.topology[self.cursor]
        self.cursor += 1
        self.nodes += 1
        self.maximum_depth = max(self.maximum_depth, depth)
        if self.nodes > MAX_TOPOLOGY_NODES_PER_ROOT:
            fail("topology exceeded per-root node guard")
        if token == "M":
            self.leaves += 1
            return Node(token)
        if token not in "skh":
            fail(f"invalid topology token {token!r} at offset {self.cursor - 1}")
        self.internal += 1
        if token == "s":
            self.split_s += 1
        elif token == "k":
            self.split_k += 1
        else:
            self.split_h += 1
        lower = self.parse(depth + 1)
        upper = self.parse(depth + 1)
        return Node(token, lower, upper)

    def finish(self) -> tuple[Node, Stats]:
        if not self.topology:
            fail("empty topology stream")
        node = self.parse()
        if self.cursor != len(self.topology):
            fail(f"trailing topology input at offset {self.cursor}")
        if self.nodes != 2 * self.leaves - 1 or self.internal != self.leaves - 1:
            fail("parsed topology is not a full binary tree")
        stats = Stats(
            self.nodes,
            self.internal,
            self.leaves,
            self.maximum_depth,
            self.split_s,
            self.split_k,
            self.split_h,
        )
        if node.packed() != self.topology:
            fail("topology parser failed exact byte reconstruction")
        return node, stats


def decode_stream(file_bytes: bytes, context: str) -> str:
    if not file_bytes.endswith(b"\n"):
        fail(f"{context} must end in exactly one newline")
    body = file_bytes[:-1]
    if not body or b"\n" in body or b"\r" in body:
        fail(f"{context} contains an empty or multi-line topology")
    try:
        topology = body.decode("ascii")
    except UnicodeDecodeError:
        fail(f"{context} must be ASCII")
    if set(topology) - ALPHABET:
        fail(f"{context} escaped the Mskh alphabet")
    return topology


def topology_stats(topology: str) -> tuple[Node, Stats]:
    return TopologyParser(topology).finish()


def node_count(node: Node) -> int:
    if node.is_leaf:
        return 1
    assert node.lower is not None and node.upper is not None
    return 1 + node_count(node.lower) + node_count(node.upper)


def leaf_count(node: Node) -> int:
    if node.is_leaf:
        return 1
    assert node.lower is not None and node.upper is not None
    return leaf_count(node.lower) + leaf_count(node.upper)


def max_depth(node: Node) -> int:
    if node.is_leaf:
        return 0
    assert node.lower is not None and node.upper is not None
    return 1 + max(max_depth(node.lower), max_depth(node.upper))


@dataclass(frozen=True, slots=True)
class PlannedNode:
    node: Node
    path: PathSteps
    lower: "PlannedNode | None" = None
    upper: "PlannedNode | None" = None

    @property
    def is_chunk(self) -> bool:
        return self.lower is None


def make_plan(node: Node, cap: int, path: PathSteps = ()) -> PlannedNode:
    if leaf_count(node) <= cap:
        return PlannedNode(node, path)
    if node.is_leaf:
        fail("a leaf exceeded the positive chunk cap")
    assert node.lower is not None and node.upper is not None
    return PlannedNode(
        node,
        path,
        make_plan(node.lower, cap, path + (Step(node.token, 0),)),
        make_plan(node.upper, cap, path + (Step(node.token, 1),)),
    )


def frontier(plan: PlannedNode) -> Iterator[PlannedNode]:
    if plan.is_chunk:
        yield plan
        return
    assert plan.lower is not None and plan.upper is not None
    yield from frontier(plan.lower)
    yield from frontier(plan.upper)


def reconstruct(plan: PlannedNode) -> str:
    if plan.is_chunk:
        return plan.node.packed()
    assert plan.lower is not None and plan.upper is not None
    return plan.node.token + reconstruct(plan.lower) + reconstruct(plan.upper)


def assembly_level(plan: PlannedNode) -> int:
    if plan.is_chunk:
        return 0
    assert plan.lower is not None and plan.upper is not None
    return 1 + max(assembly_level(plan.lower), assembly_level(plan.upper))


def nodes_by_level(plan: PlannedNode) -> dict[int, list[PlannedNode]]:
    result: dict[int, list[PlannedNode]] = {}

    def visit(current: PlannedNode) -> int:
        if current.is_chunk:
            return 0
        assert current.lower is not None and current.upper is not None
        level = 1 + max(visit(current.lower), visit(current.upper))
        result.setdefault(level, []).append(current)
        return level

    observed = visit(plan)
    if observed != assembly_level(plan):
        fail("structural layer computation drifted")
    for entries in result.values():
        entries.sort(key=lambda item: path_text(item.path))
    return result


def structural_node_count(plan: PlannedNode) -> int:
    if plan.is_chunk:
        return 0
    assert plan.lower is not None and plan.upper is not None
    return 1 + structural_node_count(plan.lower) + structural_node_count(plan.upper)


def path_text(path: PathSteps) -> str:
    return "".join(f"{step.axis}{step.branch}" for step in path) or "root"


def path_identifier(path: PathSteps) -> str:
    return "_".join(f"{step.axis}{step.branch}" for step in path) or "root"


def lean_axis(axis: str) -> str:
    mapping = {"s": ".s", "k": ".k", "h": ".chi"}
    try:
        return mapping[axis]
    except KeyError:
        fail(f"unexpected axis {axis!r}")


def lean_path(path: PathSteps) -> str:
    if not path:
        return "[]"
    values = [
        "{ axis := "
        + lean_axis(step.axis)
        + ", branch := ."
        + ("lower" if step.branch == 0 else "upper")
        + " }"
        for step in path
    ]
    return "[" + ", ".join(values) + "]"


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


@dataclass(frozen=True, slots=True)
class RootSpec:
    key: str
    stem: str
    root_lean: str
    stream_option: str
    byte_hash_option: str
    topology_hash_option: str
    s_lo: Fraction
    s_hi: Fraction
    k_lo: Fraction
    k_hi: Fraction
    h_lo: Fraction
    h_hi: Fraction


ROOT_SPECS = (
    RootSpec(
        "oneToTwo",
        "OneToTwo",
        "Auto.oneToTwoRoot",
        "one_to_two_stream",
        "one_to_two_byte_sha256",
        "one_to_two_topology_sha256",
        Fraction(1, 64),
        Fraction(1, 32),
        Fraction(1),
        Fraction(2),
        Fraction(0),
        Fraction(1),
    ),
    RootSpec(
        "twoToFour",
        "TwoToFour",
        "Auto.twoToFourRoot",
        "two_to_four_stream",
        "two_to_four_byte_sha256",
        "two_to_four_topology_sha256",
        Fraction(1, 64),
        Fraction(1, 32),
        Fraction(2),
        Fraction(4),
        Fraction(0),
        Fraction(1),
    ),
)


def bounds_at(spec: RootSpec, path: PathSteps) -> dict[str, str]:
    s_lo, s_hi = spec.s_lo, spec.s_hi
    k_lo, k_hi = spec.k_lo, spec.k_hi
    h_lo, h_hi = spec.h_lo, spec.h_hi
    for step in path:
        if step.axis == "s":
            cut = (s_lo + s_hi) / 2
            if step.branch == 0:
                s_hi = cut
            else:
                s_lo = cut
        elif step.axis == "k":
            cut = (k_lo + k_hi) / 2
            if step.branch == 0:
                k_hi = cut
            else:
                k_lo = cut
        elif step.axis == "h":
            cut = (h_lo + h_hi) / 2
            if step.branch == 0:
                h_hi = cut
            else:
                h_lo = cut
        else:
            fail(f"unexpected path axis {step.axis!r}")
    return {
        "sLo": fraction_text(s_lo),
        "sHi": fraction_text(s_hi),
        "kLo": fraction_text(k_lo),
        "kHi": fraction_text(k_hi),
        "hLo": fraction_text(h_lo),
        "hHi": fraction_text(h_hi),
    }


BASE_ROOTS: dict[str, dict[str, object]] = {
    "oneToTwo": {
        "root": {
            "sLo": 85070591730234615865843651857942052864,
            "sHi": 170141183460469231731687303715884105728,
            "kLo": 5444517870735015415413993718908291383296,
            "kHi": 10889035741470030830827987437816582766592,
            "chiLo": 0,
            "chiHi": 5444517870735015415413993718908291383296,
            "depth": 0,
        },
        "baseFile": "GeneratedUpperKHistoricalOneToTwo.tree.txt",
        "baseByteSha256": (
            "931f51c3cad73d55d07aa859307e09fbc660556725aa5505bbe473354f9142eb"
        ),
        "baseTopologySha256": (
            "5eab6fed16b66a8483698fdaa0cad196a295b540161dcd1e07eac3d06aea5aff"
        ),
        "baseStatistics": {
            "nodes": 10851,
            "internal": 5425,
            "leaves": 5426,
            "maxDepth": 14,
        },
    },
    "twoToFour": {
        "root": {
            "sLo": 85070591730234615865843651857942052864,
            "sHi": 170141183460469231731687303715884105728,
            "kLo": 10889035741470030830827987437816582766592,
            "kHi": 21778071482940061661655974875633165533184,
            "chiLo": 0,
            "chiHi": 5444517870735015415413993718908291383296,
            "depth": 0,
        },
        "baseFile": "GeneratedUpperKHistoricalTwoToFour.tree.txt",
        "baseByteSha256": (
            "ce95324f6e65db5afcb9caeb92b482178e4f707d516dba90c54cbd59981b45dd"
        ),
        "baseTopologySha256": (
            "582d1220430595af5fa50383e7bde830d4c7a618379332211cff0b2555330c3b"
        ),
        "baseStatistics": {
            "nodes": 13897,
            "internal": 6948,
            "leaves": 6949,
            "maxDepth": 14,
        },
    },
}


@dataclass(frozen=True, slots=True)
class AuthenticatedRoot:
    spec: RootSpec
    path: Path
    file_bytes: bytes
    topology: str
    tree: Node
    stats: Stats
    manifest_record: dict[str, Any]


@dataclass(frozen=True, slots=True)
class AuthenticatedBridgeReceipt:
    path: Path
    file_bytes: bytes
    document: dict[str, Any]
    payload_sha256: str
    profile_sha256: str
    aggregate_payload_sha256: str
    aggregate_input_set_sha256: str


@dataclass(frozen=True, slots=True)
class AuthenticatedInputs:
    manifest_path: Path
    manifest_bytes: bytes
    manifest: dict[str, Any]
    evaluator: dict[str, Any]
    roots: dict[str, AuthenticatedRoot]
    bridge_receipt: AuthenticatedBridgeReceipt


def validate_output_record(
    value: object, stats: Stats, topology: str, file_bytes: bytes, context: str
) -> dict[str, Any]:
    record = require_dict(value, context)
    require_exact_keys(
        record,
        {
            "nodes",
            "internal",
            "leaves",
            "maxDepth",
            "topologyBytes",
            "topologySha256",
            "byteSha256",
        },
        context,
    )
    expected = stats.output_record(topology, file_bytes)
    if record != expected:
        fail(f"{context} disagrees with the independently parsed stream")
    return record


def validate_evaluator(value: object, args: argparse.Namespace) -> dict[str, Any]:
    evaluator = require_dict(value, "patched manifest evaluator")
    require_exact_keys(
        evaluator,
        {"identity", "parameters", "configurationSha256", "sourceClosureSha256"},
        "patched manifest evaluator",
    )
    identity = require_string(evaluator["identity"], "evaluator.identity")
    if not identity:
        fail("evaluator.identity may not be empty")
    parameters = require_dict(evaluator["parameters"], "evaluator.parameters")
    require_exact_keys(
        parameters,
        {"terms", "sqrtFuel", "logFuel", "payloadPolicy", "qSecondPolicy"},
        "evaluator.parameters",
    )
    normalized = {
        "terms": require_int(parameters["terms"], "evaluator.parameters.terms", minimum=1),
        "sqrtFuel": require_int(
            parameters["sqrtFuel"], "evaluator.parameters.sqrtFuel", minimum=1
        ),
        "logFuel": require_int(
            parameters["logFuel"], "evaluator.parameters.logFuel", minimum=1
        ),
        "payloadPolicy": require_string(
            parameters["payloadPolicy"], "evaluator.parameters.payloadPolicy"
        ),
        "qSecondPolicy": require_string(
            parameters["qSecondPolicy"], "evaluator.parameters.qSecondPolicy"
        ),
    }
    if normalized != EXPECTED_EVALUATOR_PARAMETERS:
        fail("evaluator parameters differ from the hardened bridge profile")
    if normalized["terms"] != args.terms:
        fail("--terms differs from the authenticated evaluator configuration")
    if identity != EXPECTED_EVALUATOR_IDENTITY:
        fail("evaluator identity differs from the hardened bridge profile")
    configuration = require_hex64(
        evaluator["configurationSha256"], "evaluator.configurationSha256"
    )
    if configuration != sha256_bytes(canonical_json_bytes(normalized)):
        fail("evaluator.configurationSha256 does not hash its explicit parameters")
    if configuration != supplied_hex64(
        args.evaluator_configuration_sha256, "--evaluator-configuration-sha256"
    ):
        fail("supplied evaluator configuration hash does not match the manifest")
    closure = require_hex64(
        evaluator["sourceClosureSha256"], "evaluator.sourceClosureSha256"
    )
    if closure != supplied_hex64(
        args.evaluator_source_closure_sha256, "--evaluator-source-closure-sha256"
    ):
        fail("supplied evaluator source-closure hash does not match the manifest")
    return {
        "identity": identity,
        "parameters": normalized,
        "configurationSha256": configuration,
        "sourceClosureSha256": closure,
    }


def validate_patch_records(
    value: object,
    root_key: str,
    delta: dict[str, Any],
    base_nodes: int,
    base_depth: int,
) -> list[dict[str, Any]]:
    records = require_list(value, f"roots.{root_key}.patches")
    expected_keys = {
        "path",
        "oldOffset",
        "oldBoxSha256",
        "replacementTopologySha256",
        "replacementNodes",
        "replacementInternal",
        "replacementLeaves",
        "replacementMaxExtraDepth",
        "replacementLeafBoxesSha256",
        "failureRecordSha256",
        "replacementEvidenceSha256",
    }
    normalized: list[dict[str, Any]] = []
    paths: set[str] = set()
    offsets: set[int] = set()
    ordered_paths: list[str] = []
    ordered_offsets: list[int] = []
    for index, raw in enumerate(records):
        context = f"roots.{root_key}.patches[{index}]"
        record = require_dict(raw, context)
        require_exact_keys(record, expected_keys, context)
        path = require_string(record["path"], f"{context}.path")
        if re.fullmatch(r"(?:[skh][01])*", path) is None:
            fail(f"{context}.path has invalid axis/branch grammar")
        if len(path) // 2 > base_depth:
            fail(f"{context}.path exceeds the authenticated base depth")
        if path in paths:
            fail(f"{context}.path is duplicated")
        paths.add(path)
        ordered_paths.append(path)
        offset = require_int(record["oldOffset"], f"{context}.oldOffset", minimum=0)
        if offset >= base_nodes:
            fail(f"{context}.oldOffset exceeds the authenticated base stream")
        if offset in offsets:
            fail(f"{context}.oldOffset is duplicated")
        offsets.add(offset)
        ordered_offsets.append(offset)
        for field in (
            "oldBoxSha256",
            "replacementTopologySha256",
            "replacementLeafBoxesSha256",
            "failureRecordSha256",
            "replacementEvidenceSha256",
        ):
            require_hex64(record[field], f"{context}.{field}")
        for field in (
            "replacementNodes",
            "replacementInternal",
            "replacementLeaves",
            "replacementMaxExtraDepth",
        ):
            require_int(record[field], f"{context}.{field}", minimum=0)
        if (
            record["replacementNodes"] < 3
            or record["replacementInternal"] < 1
            or record["replacementLeaves"] < 2
        ):
            fail(f"{context} does not describe a nontrivial replacement")
        if record["replacementNodes"] != 2 * record["replacementLeaves"] - 1:
            fail(f"{context} replacement is not full-binary by its counts")
        if record["replacementInternal"] != record["replacementLeaves"] - 1:
            fail(f"{context} replacement internal count drifted")
        normalized.append(record)
    if ordered_offsets != sorted(ordered_offsets):
        fail(f"roots.{root_key}.patches are not strictly ordered by oldOffset")
    paths_by_length = sorted(ordered_paths, key=lambda path: (len(path), path))
    for index, ancestor in enumerate(paths_by_length):
        for descendant in paths_by_length[index + 1 :]:
            if descendant.startswith(ancestor):
                fail(
                    f"roots.{root_key}.patches contain overlapping paths "
                    f"{ancestor!r} and {descendant!r}"
                )
    if sum(record["replacementNodes"] - 1 for record in normalized) != delta["nodes"]:
        fail(f"roots.{root_key} patch node accounting disagrees with delta")
    if sum(record["replacementInternal"] for record in normalized) != delta["internal"]:
        fail(f"roots.{root_key} patch internal accounting disagrees with delta")
    if sum(record["replacementLeaves"] - 1 for record in normalized) != delta["leaves"]:
        fail(f"roots.{root_key} patch leaf accounting disagrees with delta")
    return normalized


def validate_path_text(value: object, context: str) -> str:
    path = require_string(value, context)
    if re.fullmatch(r"(?:[skh][01])*", path) is None:
        fail(f"{context} has invalid axis/branch grammar")
    return path


def path_set_sha256(paths: Iterable[str]) -> str:
    ordered = sorted(paths)
    if len(set(ordered)) != len(ordered):
        fail("cannot hash a path set containing duplicates")
    try:
        payload = "".join(path + "\n" for path in ordered).encode("ascii")
    except UnicodeEncodeError as error:
        raise ReplayPlanError("path-set digest input must be ASCII") from error
    return sha256_bytes(payload)


def relative_leaf_paths(node: Node, prefix: str = "") -> list[str]:
    if node.is_leaf:
        return [prefix]
    assert node.lower is not None and node.upper is not None
    return (
        relative_leaf_paths(node.lower, prefix + node.token + "0")
        + relative_leaf_paths(node.upper, prefix + node.token + "1")
    )


def validate_failure_evidence_root(
    value: object, root_name: str
) -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    context = f"bridge failure-evidence root {root_name}"
    root = require_dict(value, context)
    require_exact_keys(
        root,
        {
            "historicalRecords",
            "historicalRecordsSha256",
            "replacementSets",
            "replacementSetsSha256",
        },
        context,
    )
    records_value = require_list(
        root["historicalRecords"], f"{context}.historicalRecords"
    )
    normalized_records: list[dict[str, Any]] = []
    false_hashes: dict[str, str] = {}
    seen_paths: set[str] = set()
    previous_offset = -1
    for index, raw_record in enumerate(records_value):
        record_context = f"{context}.historicalRecords[{index}]"
        record = require_dict(raw_record, record_context)
        require_exact_keys(
            record, {"path", "sourceOffset", "boxSha256", "accepted"},
            record_context,
        )
        path = validate_path_text(record["path"], f"{record_context}.path")
        if path in seen_paths:
            fail(f"{record_context}.path is duplicated")
        seen_paths.add(path)
        source_offset = require_int(
            record["sourceOffset"], f"{record_context}.sourceOffset", minimum=0
        )
        if source_offset <= previous_offset:
            fail(f"{context}.historicalRecords are not in strict preorder-offset order")
        previous_offset = source_offset
        normalized = {
            "path": path,
            "sourceOffset": source_offset,
            "boxSha256": require_hex64(
                record["boxSha256"], f"{record_context}.boxSha256"
            ),
            "accepted": require_bool(
                record["accepted"], f"{record_context}.accepted"
            ),
        }
        normalized_records.append(normalized)
        if not normalized["accepted"]:
            false_hashes[path] = sha256_bytes(canonical_json_bytes(normalized))
    records_sha = require_hex64(
        root["historicalRecordsSha256"], f"{context}.historicalRecordsSha256"
    )
    if sha256_bytes(canonical_json_bytes(normalized_records)) != records_sha:
        fail(f"{context}.historicalRecordsSha256 drifted")

    sets_value = require_list(root["replacementSets"], f"{context}.replacementSets")
    normalized_sets: list[dict[str, Any]] = []
    replacements: dict[str, dict[str, Any]] = {}
    previous_patch_path: str | None = None
    for index, raw_set in enumerate(sets_value):
        set_context = f"{context}.replacementSets[{index}]"
        replacement_set = require_dict(raw_set, set_context)
        require_exact_keys(
            replacement_set,
            {"patchPath", "topologySha256", "records", "recordsSha256"},
            set_context,
        )
        patch_path = validate_path_text(
            replacement_set["patchPath"], f"{set_context}.patchPath"
        )
        if previous_patch_path is not None and patch_path <= previous_patch_path:
            fail(f"{context}.replacementSets are not strictly path-sorted")
        previous_patch_path = patch_path
        topology_sha = require_hex64(
            replacement_set["topologySha256"], f"{set_context}.topologySha256"
        )
        acceptance_value = require_list(
            replacement_set["records"], f"{set_context}.records"
        )
        if not acceptance_value:
            fail(f"{set_context}.records may not be empty")
        normalized_acceptance: list[dict[str, Any]] = []
        relative_paths: set[str] = set()
        for record_index, raw_acceptance in enumerate(acceptance_value):
            acceptance_context = f"{set_context}.records[{record_index}]"
            acceptance = require_dict(raw_acceptance, acceptance_context)
            require_exact_keys(
                acceptance, {"relativePath", "boxSha256", "accepted"},
                acceptance_context,
            )
            relative_path = validate_path_text(
                acceptance["relativePath"], f"{acceptance_context}.relativePath"
            )
            if relative_path in relative_paths:
                fail(f"{acceptance_context}.relativePath is duplicated")
            relative_paths.add(relative_path)
            if require_bool(
                acceptance["accepted"], f"{acceptance_context}.accepted"
            ) is not True:
                fail(f"{acceptance_context}.accepted must be literal true")
            normalized_acceptance.append(
                {
                    "relativePath": relative_path,
                    "boxSha256": require_hex64(
                        acceptance["boxSha256"], f"{acceptance_context}.boxSha256"
                    ),
                    "accepted": True,
                }
            )
        acceptance_sha = require_hex64(
            replacement_set["recordsSha256"], f"{set_context}.recordsSha256"
        )
        if sha256_bytes(canonical_json_bytes(normalized_acceptance)) != acceptance_sha:
            fail(f"{set_context}.recordsSha256 drifted")
        normalized_set = {
            "patchPath": patch_path,
            "topologySha256": topology_sha,
            "records": normalized_acceptance,
            "recordsSha256": acceptance_sha,
        }
        set_sha = sha256_bytes(canonical_json_bytes(normalized_set))
        normalized_sets.append(normalized_set)
        replacements[patch_path] = {**normalized_set, "setSha256": set_sha}
    sets_sha = require_hex64(
        root["replacementSetsSha256"], f"{context}.replacementSetsSha256"
    )
    if sha256_bytes(canonical_json_bytes(normalized_sets)) != sets_sha:
        fail(f"{context}.replacementSetsSha256 drifted")
    if set(replacements) != set(false_hashes):
        fail(f"{context}.replacementSets do not cover exactly the false old leaves")
    return false_hashes, replacements


def validate_bridge_patch_entry(
    value: object,
    context: str,
    guards: dict[str, int],
    false_hashes: dict[str, str],
    replacement_sets: dict[str, dict[str, Any]],
) -> tuple[str, dict[str, Any]]:
    entry = require_dict(value, context)
    require_exact_keys(
        entry,
        {
            "path",
            "oldToken",
            "oldBox",
            "oldBoxSha256",
            "failureRecordSha256",
            "replacementEvidenceSha256",
            "replacement",
        },
        context,
    )
    path = validate_path_text(entry["path"], f"{context}.path")
    if entry["oldToken"] != "M":
        fail(f"{context}.oldToken is not the old M leaf token")
    if path not in false_hashes or path not in replacement_sets:
        fail(f"{context}.path is absent from the concrete failure evidence")

    old_box = require_dict(entry["oldBox"], f"{context}.oldBox")
    box_keys = {"sLo", "sHi", "kLo", "kHi", "chiLo", "chiHi", "depth"}
    require_exact_keys(old_box, box_keys, f"{context}.oldBox")
    normalized_box = {
        key: require_int(old_box[key], f"{context}.oldBox.{key}", minimum=0)
        for key in ("sLo", "sHi", "kLo", "kHi", "chiLo", "chiHi", "depth")
    }
    if (
        normalized_box["sLo"] >= normalized_box["sHi"]
        or normalized_box["kLo"] >= normalized_box["kHi"]
        or normalized_box["chiLo"] >= normalized_box["chiHi"]
        or normalized_box["depth"] != len(path) // 2
    ):
        fail(f"{context}.oldBox is empty or has the wrong path depth")
    old_box_sha = require_hex64(
        entry["oldBoxSha256"], f"{context}.oldBoxSha256"
    )
    if sha256_bytes(canonical_json_bytes(normalized_box)) != old_box_sha:
        fail(f"{context}.oldBoxSha256 drifted")
    failure_sha = require_hex64(
        entry["failureRecordSha256"], f"{context}.failureRecordSha256"
    )
    replacement_evidence_sha = require_hex64(
        entry["replacementEvidenceSha256"],
        f"{context}.replacementEvidenceSha256",
    )
    evidence_set = replacement_sets[path]
    if (
        failure_sha != false_hashes[path]
        or replacement_evidence_sha != evidence_set["setSha256"]
    ):
        fail(f"{context} differs from its concrete failure/replacement evidence")

    replacement = require_dict(entry["replacement"], f"{context}.replacement")
    require_exact_keys(
        replacement,
        {
            "topology",
            "topologySha256",
            "nodes",
            "internal",
            "leaves",
            "maxExtraDepth",
            "leafBoxesSha256",
        },
        f"{context}.replacement",
    )
    topology = require_string(
        replacement["topology"], f"{context}.replacement.topology"
    )
    if topology == "M" or not topology.isascii():
        fail(f"{context}.replacement.topology is a no-op or is not ASCII")
    replacement_tree, replacement_stats = topology_stats(topology)
    if replacement_stats.nodes > guards["maxReplacementNodesPerPatch"]:
        fail(f"{context}.replacement exceeds the declared node guard")
    if replacement_stats.max_depth > guards["maxExtraDepthPerPatch"]:
        fail(f"{context}.replacement exceeds the declared depth guard")
    topology_sha = require_hex64(
        replacement["topologySha256"], f"{context}.replacement.topologySha256"
    )
    if (
        sha256_text(topology) != topology_sha
        or topology_sha != evidence_set["topologySha256"]
    ):
        fail(f"{context}.replacement topology hash differs from its evidence")
    declared_statistics = {
        "nodes": require_int(
            replacement["nodes"], f"{context}.replacement.nodes", minimum=1
        ),
        "internal": require_int(
            replacement["internal"], f"{context}.replacement.internal", minimum=1
        ),
        "leaves": require_int(
            replacement["leaves"], f"{context}.replacement.leaves", minimum=2
        ),
        "maxExtraDepth": require_int(
            replacement["maxExtraDepth"],
            f"{context}.replacement.maxExtraDepth",
            minimum=1,
        ),
    }
    expected_statistics = {
        "nodes": replacement_stats.nodes,
        "internal": replacement_stats.internal,
        "leaves": replacement_stats.leaves,
        "maxExtraDepth": replacement_stats.max_depth,
    }
    require_exact_json_value(
        declared_statistics, expected_statistics, f"{context}.replacement statistics"
    )
    evidence_relative_paths = [
        record["relativePath"] for record in evidence_set["records"]
    ]
    if evidence_relative_paths != relative_leaf_paths(replacement_tree):
        fail(f"{context}.replacement leaf paths differ from concrete evidence")
    leaf_boxes_sha = require_hex64(
        replacement["leafBoxesSha256"], f"{context}.replacement.leafBoxesSha256"
    )
    return path, {
        "path": path,
        "oldBoxSha256": old_box_sha,
        "replacementTopologySha256": topology_sha,
        "replacementNodes": replacement_stats.nodes,
        "replacementInternal": replacement_stats.internal,
        "replacementLeaves": replacement_stats.leaves,
        "replacementMaxExtraDepth": replacement_stats.max_depth,
        "replacementLeafBoxesSha256": leaf_boxes_sha,
        "failureRecordSha256": failure_sha,
        "replacementEvidenceSha256": replacement_evidence_sha,
    }


def validate_tool_record(
    value: object, context: str, expected_file: str
) -> dict[str, str]:
    record = require_dict(value, context)
    require_exact_keys(record, {"file", "byteSha256"}, context)
    if record["file"] != expected_file:
        fail(f"{context}.file differs from the closed tool role")
    return {
        "file": expected_file,
        "byteSha256": require_hex64(record["byteSha256"], f"{context}.byteSha256"),
    }


def validate_guard_record(value: object, context: str) -> dict[str, int]:
    record = require_dict(value, context)
    require_exact_keys(record, PATCH_GUARD_KEYS, context)
    return {
        key: require_int(record[key], f"{context}.{key}", minimum=1)
        for key in PATCH_GUARD_KEYS
    }


def json_limit_metrics(value: object, depth: int = 0) -> tuple[int, int, int]:
    maximum_depth = depth
    maximum_collection = 0
    maximum_integer_digits = 0
    if isinstance(value, dict):
        maximum_collection = len(value)
        children = value.values()
    elif isinstance(value, list):
        maximum_collection = len(value)
        children = value
    else:
        children = ()
        if isinstance(value, int) and not isinstance(value, bool):
            maximum_integer_digits = len(str(abs(value)))
    for child in children:
        child_depth, child_collection, child_digits = json_limit_metrics(
            child, depth + 1
        )
        maximum_depth = max(maximum_depth, child_depth)
        maximum_collection = max(maximum_collection, child_collection)
        maximum_integer_digits = max(maximum_integer_digits, child_digits)
    return maximum_depth, maximum_collection, maximum_integer_digits


def validate_bridge_source_closure(
    source_binding: dict[str, Any],
    aggregate_binding: dict[str, Any],
    tools: dict[str, dict[str, str]],
    evaluator: dict[str, Any],
) -> str:
    context = "bridge receipt authentication.sourceClosure"
    require_exact_keys(
        source_binding,
        {
            "file",
            "byteSha256",
            "descriptionPayloadSha256",
            "sourceClosureSha256",
            "pinnedProfileSha256",
            "projectEnvelopeFiles",
            "projectEnvelopePathsSha256",
            "evaluatorProjectFiles",
            "evaluatorPathsSha256",
            "auditLeanFiles",
            "auditPathsSha256",
            "environmentFiles",
            "mathlibBoundaryImports",
            "mathlibBoundaryImportsSha256",
            "authenticatedRepositoryFiles",
            "sourceBytes",
            "mathlibSourceTree",
            "compiledArtifactBoundary",
            "completenessBoundary",
        },
        context,
    )
    source_name = validate_bare_filename(
        source_binding["file"], f"{context}.file", ".json"
    )
    source_byte_sha = require_hex64(
        source_binding["byteSha256"], f"{context}.byteSha256"
    )
    description_payload_sha = require_hex64(
        source_binding["descriptionPayloadSha256"],
        f"{context}.descriptionPayloadSha256",
    )
    source_closure_sha = require_hex64(
        source_binding["sourceClosureSha256"], f"{context}.sourceClosureSha256"
    )
    profile_sha = require_hex64(
        source_binding["pinnedProfileSha256"], f"{context}.pinnedProfileSha256"
    )
    if (
        source_closure_sha == "0" * 64
        or profile_sha != source_closure_sha
        or profile_sha != EXPECTED_AUTHORITY_PROFILE_SHA256
    ):
        fail("bridge receipt source closure is not the nonzero pinned profile")
    exact_scalar_bindings = {
        "projectEnvelopeFiles": EXPECTED_PROJECT_ENVELOPE_FILES,
        "projectEnvelopePathsSha256": EXPECTED_PROJECT_ENVELOPE_PATHS_SHA256,
        "evaluatorProjectFiles": EXPECTED_EVALUATOR_PROJECT_FILES,
        "evaluatorPathsSha256": EXPECTED_EVALUATOR_PATHS_SHA256,
        "auditLeanFiles": EXPECTED_AUDIT_LEAN_FILES,
        "auditPathsSha256": EXPECTED_AUDIT_PATHS_SHA256,
        "environmentFiles": EXPECTED_ENVIRONMENT_FILES,
        "mathlibBoundaryImports": EXPECTED_MATHLIB_BOUNDARY_IMPORTS,
        "mathlibBoundaryImportsSha256": EXPECTED_MATHLIB_BOUNDARY_SHA256,
        "authenticatedRepositoryFiles": EXPECTED_AUTHENTICATED_REPOSITORY_FILES,
    }
    for key, expected in exact_scalar_bindings.items():
        observed = source_binding[key]
        if isinstance(expected, int):
            observed = require_int(observed, f"{context}.{key}", minimum=1)
        else:
            observed = require_hex64(observed, f"{context}.{key}")
        if observed != expected:
            fail(f"{context}.{key} differs from the reviewed closure profile")
    require_int(source_binding["sourceBytes"], f"{context}.sourceBytes", minimum=1)
    for field in ("compiledArtifactBoundary", "completenessBoundary"):
        if not require_string(source_binding[field], f"{context}.{field}"):
            fail(f"{context}.{field} may not be empty")

    tree = require_dict(source_binding["mathlibSourceTree"], f"{context}.mathlibSourceTree")
    require_exact_keys(
        tree,
        {
            "algorithm",
            "sourceTreeSha256",
            "fileCount",
            "totalBytes",
            "packageLocationKind",
            "scannerFile",
            "scannerByteSha256",
            "stabilityScansRequired",
            "snapshotSemantics",
        },
        f"{context}.mathlibSourceTree",
    )
    if tree["algorithm"] != EXPECTED_MATHLIB_TREE_ALGORITHM:
        fail("bridge receipt Mathlib source-tree algorithm drifted")
    require_hex64(tree["sourceTreeSha256"], f"{context}.mathlibSourceTree.sourceTreeSha256")
    require_int(tree["fileCount"], f"{context}.mathlibSourceTree.fileCount", minimum=1)
    require_int(tree["totalBytes"], f"{context}.mathlibSourceTree.totalBytes", minimum=1)
    if tree["packageLocationKind"] not in ("directory", "symlink"):
        fail("bridge receipt Mathlib package-location kind is unknown")
    if tree["scannerFile"] != CLOSURE_PROFILE_GENERATOR_TOOL:
        fail("bridge receipt Mathlib scanner file drifted")
    scanner_sha = require_hex64(
        tree["scannerByteSha256"], f"{context}.mathlibSourceTree.scannerByteSha256"
    )
    if scanner_sha != tools["closureProfileGenerator"]["byteSha256"]:
        fail("bridge receipt Mathlib scanner/tool hashes differ")
    if require_int(
        tree["stabilityScansRequired"],
        f"{context}.mathlibSourceTree.stabilityScansRequired",
        minimum=1,
    ) != EXPECTED_MATHLIB_STABILITY_SCANS:
        fail("bridge receipt does not require the reviewed two Mathlib scans")
    if not require_string(
        tree["snapshotSemantics"], f"{context}.mathlibSourceTree.snapshotSemantics"
    ):
        fail("bridge receipt Mathlib snapshot semantics may not be empty")

    source_path = direct_scratch_reference(
        source_name, "bridge source-closure description", ".json"
    )
    source_bytes = read_regular_file(
        source_path,
        "bridge source-closure description",
        MAX_CLOSURE_DESCRIPTION_BYTES,
    )
    if sha256_bytes(source_bytes) != source_byte_sha:
        fail("bridge source-closure description byte hash differs from receipt")
    description = parse_json(source_bytes, "bridge source-closure description")
    require_canonical_json_file(source_bytes, description, "bridge source-closure description")
    require_exact_keys(
        description,
        {
            "schemaVersion",
            "kind",
            "closurePolicy",
            "evaluator",
            "closureProfile",
            "aggregateBinding",
            "auditCommitments",
            "sourceClosureSha256",
            "descriptionPayloadSha256",
        },
        "bridge source-closure description",
    )
    if require_int(description["schemaVersion"], "source-closure schemaVersion") != 1:
        fail("bridge source-closure schemaVersion drifted")
    if description["kind"] != (
        "upper-k-historical-authoritative-evaluator-source-closure"
    ):
        fail("bridge source-closure kind drifted")
    if description["closurePolicy"] != EXPECTED_CLOSURE_POLICY:
        fail("bridge source-closure policy drifted")
    declared_description_sha = require_hex64(
        description["descriptionPayloadSha256"],
        "source-closure descriptionPayloadSha256",
    )
    description_payload = dict(description)
    del description_payload["descriptionPayloadSha256"]
    if (
        sha256_bytes(canonical_json_bytes(description_payload))
        != declared_description_sha
        or declared_description_sha != description_payload_sha
    ):
        fail("bridge source-closure description payload hash drifted")
    if require_hex64(
        description["sourceClosureSha256"], "source-closure sourceClosureSha256"
    ) != source_closure_sha:
        fail("bridge source-closure description/profile binding drifted")
    expected_description_evaluator = {
        key: evaluator[key]
        for key in ("identity", "parameters", "configurationSha256")
    }
    if description["evaluator"] != expected_description_evaluator:
        fail("bridge source-closure evaluator differs from PatchApplier result")

    profile = require_dict(description["closureProfile"], "source-closure closureProfile")
    require_exact_keys(
        profile,
        {
            "schemaVersion",
            "profileId",
            "projectInventory",
            "evaluatorClosure",
            "auditRunnerClosure",
            "environmentBinding",
            "profilePayloadSha256",
        },
        "source-closure closureProfile",
    )
    if (
        require_int(profile["schemaVersion"], "closure profile schemaVersion") != 1
        or profile["profileId"] != EXPECTED_PROFILE_ID
    ):
        fail("bridge closure-profile identity drifted")
    declared_profile_sha = require_hex64(
        profile["profilePayloadSha256"], "closure profile profilePayloadSha256"
    )
    profile_payload = dict(profile)
    del profile_payload["profilePayloadSha256"]
    if (
        sha256_bytes(canonical_json_bytes(profile_payload)) != declared_profile_sha
        or declared_profile_sha != profile_sha
    ):
        fail("bridge closure-profile payload hash differs from receipt authority")

    inventory = require_dict(
        profile["projectInventory"], "closure profile projectInventory"
    )
    require_exact_keys(
        inventory,
        {"role", "count", "pathsSha256", "recordsSha256", "records"},
        "closure profile projectInventory",
    )
    inventory_records = require_list(
        inventory["records"], "closure profile projectInventory.records"
    )
    if (
        require_int(inventory["count"], "closure profile projectInventory.count")
        != source_binding["projectEnvelopeFiles"]
        or len(inventory_records) != source_binding["projectEnvelopeFiles"]
        or require_hex64(
            inventory["pathsSha256"],
            "closure profile projectInventory.pathsSha256",
        )
        != source_binding["projectEnvelopePathsSha256"]
    ):
        fail("closure profile project inventory differs from receipt summary")
    require_hex64(
        inventory["recordsSha256"],
        "closure profile projectInventory.recordsSha256",
    )
    if not require_string(
        inventory["role"], "closure profile projectInventory.role"
    ):
        fail("closure profile projectInventory.role may not be empty")

    evaluator_closure = require_dict(
        profile["evaluatorClosure"], "closure profile evaluatorClosure"
    )
    require_exact_keys(
        evaluator_closure,
        {
            "root",
            "rootDeclaration",
            "projectFileCount",
            "paths",
            "pathsSha256",
            "recordsSha256",
        },
        "closure profile evaluatorClosure",
    )
    evaluator_paths = require_list(
        evaluator_closure["paths"], "closure profile evaluatorClosure.paths"
    )
    if (
        evaluator_closure["rootDeclaration"] != EXPECTED_EVALUATOR_IDENTITY
        or require_int(
            evaluator_closure["projectFileCount"],
            "closure profile evaluatorClosure.projectFileCount",
        )
        != source_binding["evaluatorProjectFiles"]
        or len(evaluator_paths) != source_binding["evaluatorProjectFiles"]
        or require_hex64(
            evaluator_closure["pathsSha256"],
            "closure profile evaluatorClosure.pathsSha256",
        )
        != source_binding["evaluatorPathsSha256"]
    ):
        fail("closure profile evaluator closure differs from receipt summary")
    if not require_string(
        evaluator_closure["root"], "closure profile evaluatorClosure.root"
    ):
        fail("closure profile evaluatorClosure.root may not be empty")
    require_hex64(
        evaluator_closure["recordsSha256"],
        "closure profile evaluatorClosure.recordsSha256",
    )

    audit_closure = require_dict(
        profile["auditRunnerClosure"], "closure profile auditRunnerClosure"
    )
    require_exact_keys(
        audit_closure,
        {
            "root",
            "projectRoot",
            "projectFileCount",
            "scratchFileCount",
            "totalLeanFileCount",
            "projectPathsSha256",
            "scratchRecords",
            "scratchPathsSha256",
            "scratchRecordsSha256",
            "totalPathsSha256",
        },
        "closure profile auditRunnerClosure",
    )
    scratch_records = require_list(
        audit_closure["scratchRecords"],
        "closure profile auditRunnerClosure.scratchRecords",
    )
    if (
        require_int(
            audit_closure["projectFileCount"],
            "closure profile auditRunnerClosure.projectFileCount",
        )
        != source_binding["projectEnvelopeFiles"]
        or require_int(
            audit_closure["scratchFileCount"],
            "closure profile auditRunnerClosure.scratchFileCount",
        )
        != 3
        or len(scratch_records) != 3
        or require_int(
            audit_closure["totalLeanFileCount"],
            "closure profile auditRunnerClosure.totalLeanFileCount",
        )
        != source_binding["auditLeanFiles"]
        or require_hex64(
            audit_closure["projectPathsSha256"],
            "closure profile auditRunnerClosure.projectPathsSha256",
        )
        != source_binding["projectEnvelopePathsSha256"]
        or require_hex64(
            audit_closure["totalPathsSha256"],
            "closure profile auditRunnerClosure.totalPathsSha256",
        )
        != source_binding["auditPathsSha256"]
    ):
        fail("closure profile audit closure differs from receipt summary")
    for field in ("root", "projectRoot"):
        if not require_string(
            audit_closure[field], f"closure profile auditRunnerClosure.{field}"
        ):
            fail(f"closure profile auditRunnerClosure.{field} may not be empty")
    for field in ("scratchPathsSha256", "scratchRecordsSha256"):
        require_hex64(
            audit_closure[field], f"closure profile auditRunnerClosure.{field}"
        )

    environment = require_dict(
        profile["environmentBinding"], "closure profile environmentBinding"
    )
    require_exact_keys(
        environment,
        {
            "profileId",
            "files",
            "filesSha256",
            "leanToolchain",
            "mathlibPackage",
            "mathlibBoundaryImports",
            "environmentPayloadSha256",
        },
        "closure profile environmentBinding",
    )
    environment_files = require_list(
        environment["files"], "closure profile environmentBinding.files"
    )
    if len(environment_files) != source_binding["environmentFiles"]:
        fail("closure profile environment-file count differs from receipt summary")
    if not require_string(
        environment["profileId"], "closure profile environmentBinding.profileId"
    ) or not require_string(
        environment["leanToolchain"],
        "closure profile environmentBinding.leanToolchain",
    ):
        fail("closure profile environment identity may not be empty")
    require_hex64(
        environment["filesSha256"],
        "closure profile environmentBinding.filesSha256",
    )
    environment_payload_sha = require_hex64(
        environment["environmentPayloadSha256"],
        "closure profile environmentBinding.environmentPayloadSha256",
    )
    environment_payload = dict(environment)
    del environment_payload["environmentPayloadSha256"]
    if sha256_bytes(canonical_json_bytes(environment_payload)) != environment_payload_sha:
        fail("closure profile environment payload hash drifted")

    mathlib_package = require_dict(
        environment["mathlibPackage"],
        "closure profile environmentBinding.mathlibPackage",
    )
    require_exact_keys(
        mathlib_package,
        {
            "name",
            "url",
            "type",
            "rev",
            "inputRev",
            "manifestFile",
            "configFile",
            "sourceTreeSha256",
        },
        "closure profile environmentBinding.mathlibPackage",
    )
    profile_tree_sha = require_hex64(
        mathlib_package["sourceTreeSha256"],
        "closure profile environmentBinding.mathlibPackage.sourceTreeSha256",
    )
    if profile_tree_sha == "0" * 64 or profile_tree_sha != tree["sourceTreeSha256"]:
        fail("receipt Mathlib source-tree digest differs from the pinned profile")
    for field in ("name", "url", "type", "rev", "inputRev", "manifestFile", "configFile"):
        if not require_string(
            mathlib_package[field],
            f"closure profile environmentBinding.mathlibPackage.{field}",
        ):
            fail(f"closure profile Mathlib package field {field} may not be empty")

    boundary = require_dict(
        environment["mathlibBoundaryImports"],
        "closure profile environmentBinding.mathlibBoundaryImports",
    )
    require_exact_keys(
        boundary,
        {"count", "modules", "modulesSha256"},
        "closure profile environmentBinding.mathlibBoundaryImports",
    )
    boundary_modules = require_list(
        boundary["modules"],
        "closure profile environmentBinding.mathlibBoundaryImports.modules",
    )
    if (
        require_int(
            boundary["count"],
            "closure profile environmentBinding.mathlibBoundaryImports.count",
        )
        != source_binding["mathlibBoundaryImports"]
        or len(boundary_modules) != source_binding["mathlibBoundaryImports"]
        or require_hex64(
            boundary["modulesSha256"],
            "closure profile environmentBinding.mathlibBoundaryImports.modulesSha256",
        )
        != source_binding["mathlibBoundaryImportsSha256"]
    ):
        fail("closure profile Mathlib boundary differs from receipt summary")

    description_aggregate = require_dict(
        description["aggregateBinding"], "source-closure aggregateBinding"
    )
    require_exact_keys(
        description_aggregate,
        {"file", "byteSha256", "aggregatePayloadSha256", "converterPayloadSha256"},
        "source-closure aggregateBinding",
    )
    expected_description_aggregate = {
        key: aggregate_binding[key]
        for key in (
            "file",
            "byteSha256",
            "aggregatePayloadSha256",
            "converterPayloadSha256",
        )
    }
    if description_aggregate != expected_description_aggregate:
        fail("bridge source-closure and receipt aggregate bindings differ")

    commitments = require_dict(
        description["auditCommitments"], "source-closure auditCommitments"
    )
    require_exact_keys(
        commitments,
        {
            "bridge",
            "aggregator",
            "patchApplier",
            "closureProfileGenerator",
            "authenticatedRangeEvaluatorCommitments",
            "authenticatedRangeEvaluatorCommitmentsSha256",
        },
        "source-closure auditCommitments",
    )
    for role in ("bridge", "aggregator", "patchApplier", "closureProfileGenerator"):
        if commitments[role] != tools[role]:
            fail(f"source-closure and receipt tool commitment differ at {role}")
    range_commitments = require_dict(
        commitments["authenticatedRangeEvaluatorCommitments"],
        "source-closure authenticated range commitments",
    )
    range_sha = require_hex64(
        commitments["authenticatedRangeEvaluatorCommitmentsSha256"],
        "source-closure authenticated range commitments hash",
    )
    if sha256_bytes(canonical_json_bytes(range_commitments)) != range_sha:
        fail("source-closure authenticated range commitment hash drifted")
    return profile_sha


def authenticate_bridge_receipt(
    args: argparse.Namespace,
    manifest_path: Path,
    manifest: dict[str, Any],
    evaluator: dict[str, Any],
    roots: dict[str, AuthenticatedRoot],
) -> AuthenticatedBridgeReceipt:
    receipt_path = direct_scratch_input(
        args.bridge_receipt, "--bridge-receipt", ".json"
    )
    receipt_bytes = read_regular_file(
        receipt_path, "hardened bridge receipt", MAX_RECEIPT_BYTES
    )
    receipt_byte_sha = sha256_bytes(receipt_bytes)
    if receipt_byte_sha != supplied_hex64(
        args.bridge_receipt_sha256, "--bridge-receipt-sha256"
    ):
        fail("bridge receipt byte hash differs from the supplied authority")
    receipt = parse_json(receipt_bytes, "hardened bridge receipt")
    require_canonical_json_file(receipt_bytes, receipt, "hardened bridge receipt")
    require_exact_keys(
        receipt,
        {
            "schemaVersion",
            "kind",
            "status",
            "tool",
            "authentication",
            "outputs",
            "currentPatchApplierCeilings",
            "requiredGuards",
            "actualMetrics",
            "exceededCeilings",
            "rootBindings",
            "receiptHashRule",
            "receiptPayloadSha256",
        },
        "hardened bridge receipt",
    )
    if require_int(receipt["schemaVersion"], "bridge receipt schemaVersion") != 1:
        fail("unsupported bridge receipt schemaVersion")
    if receipt["kind"] != "upper-k-historical-exact-patch-bridge-receipt":
        fail("unexpected bridge receipt kind")
    if receipt["status"] != READY_RECEIPT_STATUS:
        fail("bridge receipt is not ready for the current PatchApplier")
    if receipt["tool"] != BRIDGE_TOOL:
        fail("bridge receipt tool identity drifted")
    exceeded = require_list(receipt["exceededCeilings"], "bridge receipt exceededCeilings")
    if exceeded:
        fail("bridge receipt reports exceeded PatchApplier ceilings")
    if receipt["receiptHashRule"] != RECEIPT_HASH_RULE:
        fail("bridge receipt payload-hash rule drifted")
    receipt_payload_sha = require_hex64(
        receipt["receiptPayloadSha256"], "bridge receipt receiptPayloadSha256"
    )
    if receipt_payload_sha != supplied_hex64(
        args.bridge_receipt_payload_sha256,
        "--bridge-receipt-payload-sha256",
    ):
        fail("bridge receipt payload hash differs from the supplied authority")
    receipt_payload = dict(receipt)
    del receipt_payload["receiptPayloadSha256"]
    if sha256_bytes(canonical_json_bytes(receipt_payload)) != receipt_payload_sha:
        fail("bridge receipt canonical payload hash drifted")

    authentication = require_dict(receipt["authentication"], "bridge receipt authentication")
    require_exact_keys(
        authentication,
        {"aggregate", "sourceClosure", "tools"},
        "bridge receipt authentication",
    )
    aggregate_binding = require_dict(
        authentication["aggregate"], "bridge receipt authentication.aggregate"
    )
    require_exact_keys(
        aggregate_binding,
        {
            "file",
            "byteSha256",
            "aggregatePayloadSha256",
            "inputSetSha256",
            "converterPayloadSha256",
        },
        "bridge receipt authentication.aggregate",
    )
    validate_bare_filename(
        aggregate_binding["file"], "bridge receipt aggregate file", ".json"
    )
    for field in (
        "byteSha256",
        "aggregatePayloadSha256",
        "inputSetSha256",
        "converterPayloadSha256",
    ):
        require_hex64(
            aggregate_binding[field], f"bridge receipt authentication.aggregate.{field}"
        )

    tools_value = require_dict(authentication["tools"], "bridge receipt authentication.tools")
    require_exact_keys(
        tools_value,
        {"bridge", "aggregator", "patchApplier", "closureProfileGenerator"},
        "bridge receipt authentication.tools",
    )
    tools = {
        "bridge": validate_tool_record(
            tools_value["bridge"], "bridge receipt tool bridge", BRIDGE_TOOL
        ),
        "aggregator": validate_tool_record(
            tools_value["aggregator"], "bridge receipt tool aggregator", AGGREGATOR_TOOL
        ),
        "patchApplier": validate_tool_record(
            tools_value["patchApplier"],
            "bridge receipt tool patchApplier",
            PATCH_APPLIER_TOOL,
        ),
        "closureProfileGenerator": validate_tool_record(
            tools_value["closureProfileGenerator"],
            "bridge receipt tool closureProfileGenerator",
            CLOSURE_PROFILE_GENERATOR_TOOL,
        ),
    }
    for role, tool in tools.items():
        tool_path = direct_scratch_reference(
            tool["file"], f"bridge receipt tool {role}", ".py"
        )
        tool_bytes = read_regular_file(
            tool_path, f"bridge receipt tool source {role}", MAX_TOOL_BYTES
        )
        if sha256_bytes(tool_bytes) != tool["byteSha256"]:
            fail(f"bridge receipt tool source hash drifted at closed role {role}")
    if manifest["tool"] != tools["patchApplier"]["file"]:
        fail("PatchApplier result and bridge receipt tool roles differ")
    source_binding = require_dict(
        authentication["sourceClosure"], "bridge receipt authentication.sourceClosure"
    )
    profile_sha = validate_bridge_source_closure(
        source_binding, aggregate_binding, tools, evaluator
    )
    if evaluator["sourceClosureSha256"] != profile_sha:
        fail("PatchApplier evaluator closure differs from bridge pinned profile")

    required_guards = validate_guard_record(
        receipt["requiredGuards"], "bridge receipt requiredGuards"
    )
    current_ceilings = validate_guard_record(
        receipt["currentPatchApplierCeilings"],
        "bridge receipt currentPatchApplierCeilings",
    )
    if current_ceilings != EXPECTED_PATCH_APPLIER_CEILINGS:
        fail("bridge receipt current PatchApplier ceilings differ from reviewed source")
    if required_guards != manifest["guards"]:
        fail("bridge required guards differ from PatchApplier result guards")
    for name in PATCH_GUARD_KEYS:
        if required_guards[name] > current_ceilings[name]:
            fail(f"ready bridge receipt exceeds current PatchApplier ceiling {name}")

    outputs = require_dict(receipt["outputs"], "bridge receipt outputs")
    require_exact_keys(
        outputs,
        {"failureEvidence", "patchManifest", "receipt", "stage", "futurePatchApplierOutputs"},
        "bridge receipt outputs",
    )
    failure_output = require_dict(outputs["failureEvidence"], "bridge receipt failureEvidence output")
    require_exact_keys(
        failure_output, {"file", "byteSha256", "bytes"},
        "bridge receipt failureEvidence output",
    )
    failure_name = validate_bare_filename(
        failure_output["file"], "bridge receipt failureEvidence output file", ".json"
    )
    failure_sha = require_hex64(
        failure_output["byteSha256"], "bridge receipt failureEvidence output byteSha256"
    )
    failure_size = require_int(
        failure_output["bytes"], "bridge receipt failureEvidence output bytes", minimum=1
    )
    patch_output = require_dict(outputs["patchManifest"], "bridge receipt patchManifest output")
    require_exact_keys(
        patch_output, {"file", "byteSha256", "payloadSha256", "bytes"},
        "bridge receipt patchManifest output",
    )
    patch_name = validate_bare_filename(
        patch_output["file"], "bridge receipt patchManifest output file", ".json"
    )
    patch_sha = require_hex64(
        patch_output["byteSha256"], "bridge receipt patchManifest output byteSha256"
    )
    patch_payload_sha = require_hex64(
        patch_output["payloadSha256"], "bridge receipt patchManifest output payloadSha256"
    )
    patch_size = require_int(
        patch_output["bytes"], "bridge receipt patchManifest output bytes", minimum=1
    )
    if manifest["failureEvidence"] != {
        "file": failure_name,
        "byteSha256": failure_sha,
        "configurationSha256": evaluator["configurationSha256"],
    }:
        fail("bridge failure-evidence output differs from PatchApplier result")
    if manifest["patchManifest"] != {
        "file": patch_name,
        "byteSha256": patch_sha,
        "payloadSha256": patch_payload_sha,
    }:
        fail("bridge patch-manifest output differs from PatchApplier result")
    receipt_output = require_dict(outputs["receipt"], "bridge receipt self output")
    require_exact_keys(receipt_output, {"file"}, "bridge receipt self output")
    if validate_bare_filename(
        receipt_output["file"], "bridge receipt self output file", ".json"
    ) != receipt_path.name:
        fail("bridge receipt self filename differs from the supplied receipt")
    stage_output = require_dict(outputs["stage"], "bridge receipt stage output")
    require_exact_keys(stage_output, {"file"}, "bridge receipt stage output")
    validate_bare_filename(stage_output["file"], "bridge receipt stage output file", ".json")

    future = require_dict(
        outputs["futurePatchApplierOutputs"], "bridge future PatchApplier outputs"
    )
    require_exact_keys(
        future, {"resultManifestFile", "roots"}, "bridge future PatchApplier outputs"
    )
    if validate_bare_filename(
        future["resultManifestFile"],
        "bridge future PatchApplier result manifest",
        ".manifest.json",
    ) != manifest_path.name:
        fail("bridge-planned result manifest differs from the supplied result")
    future_roots = require_dict(future["roots"], "bridge future PatchApplier roots")
    if set(future_roots) != set(ROOT_KEYS):
        fail("bridge future PatchApplier root set drifted")
    for root_name in ROOT_KEYS:
        root_output = require_dict(
            future_roots[root_name], f"bridge future root {root_name}"
        )
        require_exact_keys(
            root_output, {"file", "expectedOutput"}, f"bridge future root {root_name}"
        )
        if root_output["file"] != roots[root_name].path.name:
            fail(f"bridge future root filename differs from supplied stream: {root_name}")
        if root_output["file"] != manifest["roots"][root_name]["outputFile"]:
            fail(f"bridge/result root filename differs: {root_name}")
        if root_output["expectedOutput"] != manifest["roots"][root_name]["output"]:
            fail(f"bridge/result expected root output differs: {root_name}")

    failure_path = direct_scratch_reference(
        failure_name, "bridge failure-evidence artifact", ".json"
    )
    failure_bytes = read_regular_file(
        failure_path, "bridge failure-evidence artifact", MAX_MANIFEST_BYTES
    )
    if len(failure_bytes) != failure_size or sha256_bytes(failure_bytes) != failure_sha:
        fail("bridge failure-evidence artifact bytes differ from receipt")
    evidence = parse_json(failure_bytes, "bridge failure-evidence artifact")
    require_canonical_json_file(failure_bytes, evidence, "bridge failure-evidence artifact")
    require_exact_keys(
        evidence, {"schemaVersion", "kind", "base", "evaluator", "roots"},
        "bridge failure-evidence artifact",
    )
    if (
        require_int(evidence["schemaVersion"], "failure evidence schemaVersion") != 1
        or evidence["kind"] != "upper-k-historical-concrete-leaf-evidence"
    ):
        fail("bridge failure-evidence identity/base/evaluator drifted")
    require_exact_json_value(
        evidence["base"], manifest["base"], "bridge failure-evidence base"
    )
    require_exact_json_value(
        evidence["evaluator"], evaluator, "bridge failure-evidence evaluator"
    )
    evidence_roots = require_dict(evidence["roots"], "bridge failure-evidence roots")
    if set(evidence_roots) != set(ROOT_KEYS):
        fail("bridge failure-evidence root set drifted")

    patch_path = direct_scratch_reference(
        patch_name, "bridge patch-manifest artifact", ".json"
    )
    patch_bytes = read_regular_file(
        patch_path, "bridge patch-manifest artifact", MAX_MANIFEST_BYTES
    )
    if len(patch_bytes) != patch_size or sha256_bytes(patch_bytes) != patch_sha:
        fail("bridge patch-manifest artifact bytes differ from receipt")
    patch_document = parse_json(patch_bytes, "bridge patch-manifest artifact")
    require_canonical_json_file(patch_bytes, patch_document, "bridge patch-manifest artifact")
    require_exact_keys(
        patch_document,
        {
            "schemaVersion",
            "kind",
            "base",
            "evaluator",
            "failureEvidence",
            "guards",
            "resultManifestFile",
            "roots",
            "manifestPayloadSha256",
        },
        "bridge patch-manifest artifact",
    )
    declared_patch_payload = require_hex64(
        patch_document["manifestPayloadSha256"],
        "bridge patch-manifest manifestPayloadSha256",
    )
    patch_payload = dict(patch_document)
    del patch_payload["manifestPayloadSha256"]
    if (
        sha256_bytes(canonical_json_bytes(patch_payload)) != declared_patch_payload
        or declared_patch_payload != patch_payload_sha
    ):
        fail("bridge patch-manifest canonical payload hash drifted")
    if (
        require_int(patch_document["schemaVersion"], "patch manifest schemaVersion") != 1
        or patch_document["kind"] != "upper-k-historical-path-patch"
        or patch_document["resultManifestFile"] != manifest_path.name
    ):
        fail("bridge patch-manifest/result identity or binding drifted")
    require_exact_json_value(
        patch_document["base"], manifest["base"], "bridge patch-manifest base"
    )
    require_exact_json_value(
        patch_document["evaluator"], evaluator, "bridge patch-manifest evaluator"
    )
    require_exact_json_value(
        patch_document["failureEvidence"],
        manifest["failureEvidence"],
        "bridge patch-manifest failureEvidence",
    )
    patch_guards = validate_guard_record(
        patch_document["guards"], "bridge patch-manifest guards"
    )
    if patch_guards != required_guards:
        fail("bridge patch-manifest guards differ from the receipt/result guards")
    patch_roots = require_dict(patch_document["roots"], "bridge patch-manifest roots")
    if set(patch_roots) != set(ROOT_KEYS):
        fail("bridge patch-manifest root set drifted")

    root_bindings = require_dict(receipt["rootBindings"], "bridge receipt rootBindings")
    if set(root_bindings) != set(ROOT_KEYS):
        fail("bridge receipt root binding set drifted")
    for root_name in ROOT_KEYS:
        root_binding = require_dict(root_bindings[root_name], f"bridge root binding {root_name}")
        require_exact_keys(
            root_binding,
            {
                "historicalRecordsSha256",
                "replacementSetsSha256",
                "failedPathsSha256",
                "expectedOutput",
            },
            f"bridge root binding {root_name}",
        )
        evidence_root = require_dict(
            evidence_roots[root_name], f"bridge failure-evidence root {root_name}"
        )
        false_hashes, replacement_sets = validate_failure_evidence_root(
            evidence_root, root_name
        )
        patch_root = require_dict(
            patch_roots[root_name], f"bridge patch-manifest root {root_name}"
        )
        require_exact_keys(
            patch_root,
            {
                "baseTopologySha256",
                "baseNodes",
                "baseLeaves",
                "outputFile",
                "failedLeafCount",
                "failedPathsSha256",
                "patches",
                "expectedOutput",
            },
            f"bridge patch-manifest root {root_name}",
        )
        for field in (
            "historicalRecordsSha256",
            "replacementSetsSha256",
            "failedPathsSha256",
        ):
            require_hex64(root_binding[field], f"bridge root binding {root_name}.{field}")
        if (
            root_binding["historicalRecordsSha256"]
            != evidence_root["historicalRecordsSha256"]
            or root_binding["replacementSetsSha256"]
            != evidence_root["replacementSetsSha256"]
            or root_binding["failedPathsSha256"] != patch_root["failedPathsSha256"]
            or root_binding["expectedOutput"] != patch_root["expectedOutput"]
            or root_binding["expectedOutput"] != manifest["roots"][root_name]["output"]
        ):
            fail(f"bridge receipt/evidence/patch/result root binding drifted: {root_name}")
        if (
            patch_root["outputFile"] != roots[root_name].path.name
            or patch_root["outputFile"] != manifest["roots"][root_name]["outputFile"]
            or patch_root["baseTopologySha256"]
            != manifest["roots"][root_name]["baseTopologySha256"]
            or patch_root["baseNodes"]
            != manifest["roots"][root_name]["baseStatistics"]["nodes"]
            or patch_root["baseLeaves"]
            != manifest["roots"][root_name]["baseStatistics"]["leaves"]
        ):
            fail(f"bridge patch/result root metadata drifted: {root_name}")
        patch_entries = require_list(
            patch_root["patches"], f"bridge patch-manifest root {root_name}.patches"
        )
        result_entries = require_list(
            manifest["roots"][root_name]["patches"],
            f"PatchApplier result root {root_name}.patches",
        )
        validated_patch_entries: dict[str, dict[str, Any]] = {}
        patch_paths: list[str] = []
        for index, item in enumerate(patch_entries):
            path, expected_result = validate_bridge_patch_entry(
                item,
                f"bridge patch-manifest root {root_name}.patches[{index}]",
                required_guards,
                false_hashes,
                replacement_sets,
            )
            if path in validated_patch_entries:
                fail(f"bridge patch-manifest root {root_name} duplicates path {path!r}")
            validated_patch_entries[path] = expected_result
            patch_paths.append(path)
        result_by_path = {item["path"]: item for item in result_entries}
        result_paths = list(result_by_path)
        if (
            require_int(
                patch_root["failedLeafCount"],
                f"bridge patch-manifest root {root_name}.failedLeafCount",
            )
            != len(patch_entries)
            or len(set(patch_paths)) != len(patch_paths)
            or set(patch_paths) != set(result_paths)
            or set(patch_paths) != set(false_hashes)
            or path_set_sha256(patch_paths) != patch_root["failedPathsSha256"]
        ):
            fail(f"bridge patch/result failed-path set drifted: {root_name}")
        for path, expected_result in validated_patch_entries.items():
            result_record = result_by_path[path]
            for field, expected_value in expected_result.items():
                require_exact_json_value(
                    result_record[field],
                    expected_value,
                    f"PatchApplier result root {root_name} path {path!r}.{field}",
                )

    actual_metrics = require_dict(receipt["actualMetrics"], "bridge receipt actualMetrics")
    require_exact_keys(
        actual_metrics,
        {
            "totalPatches",
            "patchesPerRoot",
            "maximumExtraDepthPerPatch",
            "maximumReplacementNodesPerPatch",
            "totalAddedInternal",
            "finalNodesPerRoot",
            "combinedFinalNodes",
            "patchedDepthPerRoot",
            "representation",
        },
        "bridge receipt actualMetrics",
    )
    patch_counts = {
        root_name: len(manifest["roots"][root_name]["patches"])
        for root_name in ROOT_KEYS
    }
    replacement_nodes = [
        patch["replacementNodes"]
        for root_name in ROOT_KEYS
        for patch in manifest["roots"][root_name]["patches"]
    ]
    replacement_depths = [
        patch["replacementMaxExtraDepth"]
        for root_name in ROOT_KEYS
        for patch in manifest["roots"][root_name]["patches"]
    ]
    total_added_internal = sum(
        patch["replacementInternal"]
        for root_name in ROOT_KEYS
        for patch in manifest["roots"][root_name]["patches"]
    )
    final_nodes = {
        root_name: roots[root_name].stats.nodes for root_name in ROOT_KEYS
    }
    final_depths = {
        root_name: roots[root_name].stats.max_depth for root_name in ROOT_KEYS
    }
    expected_metrics_without_representation = {
        "totalPatches": sum(patch_counts.values()),
        "patchesPerRoot": patch_counts,
        "maximumExtraDepthPerPatch": max(replacement_depths, default=0),
        "maximumReplacementNodesPerPatch": max(replacement_nodes, default=0),
        "totalAddedInternal": total_added_internal,
        "finalNodesPerRoot": final_nodes,
        "combinedFinalNodes": sum(final_nodes.values()),
        "patchedDepthPerRoot": final_depths,
    }
    for key, expected in expected_metrics_without_representation.items():
        require_exact_json_value(
            actual_metrics[key], expected,
            f"bridge receipt actual metric {key}",
        )
    expected_required_guards = {
        "maxPatchesPerRoot": max(1, max(patch_counts.values())),
        "maxExtraDepthPerPatch": max(1, max(replacement_depths, default=0)),
        "maxReplacementNodesPerPatch": max(1, max(replacement_nodes, default=0)),
        "maxTotalAddedInternal": max(1, total_added_internal),
        "maxFinalNodesPerRoot": max(final_nodes.values()),
        "maxCombinedFinalNodes": sum(final_nodes.values()),
        "maxPatchedDepth": max(final_depths.values()),
    }
    if required_guards != expected_required_guards:
        fail("bridge required guards are not the exact result-derived minima")

    representation = require_dict(
        actual_metrics["representation"], "bridge receipt representation metrics"
    )
    require_exact_keys(
        representation, {"fileSizes", "jsonStructure"},
        "bridge receipt representation metrics",
    )
    file_sizes = require_dict(
        representation["fileSizes"], "bridge receipt representation fileSizes"
    )
    require_exact_keys(
        file_sizes, {"failureEvidenceBytes", "patchManifestBytes"},
        "bridge receipt representation fileSizes",
    )
    require_exact_json_value(
        file_sizes,
        {
            "failureEvidenceBytes": len(failure_bytes),
            "patchManifestBytes": len(patch_bytes),
        },
        "bridge receipt representation fileSizes",
    )
    structure = require_dict(
        representation["jsonStructure"], "bridge receipt representation jsonStructure"
    )
    require_exact_keys(
        structure, {"failureEvidence", "patchManifest"},
        "bridge receipt representation jsonStructure",
    )
    for artifact, value in (("failureEvidence", evidence), ("patchManifest", patch_document)):
        metrics = require_dict(
            structure[artifact], f"bridge receipt representation {artifact}"
        )
        require_exact_keys(
            metrics,
            {"maximumNestingDepth", "maximumCollectionItems", "maximumIntegerDigits"},
            f"bridge receipt representation {artifact}",
        )
        observed = json_limit_metrics(value)
        expected = {
            "maximumNestingDepth": observed[0],
            "maximumCollectionItems": observed[1],
            "maximumIntegerDigits": observed[2],
        }
        require_exact_json_value(
            metrics, expected, f"bridge receipt representation {artifact}"
        )
        if (
            observed[0] > MAX_JSON_NESTING
            or observed[1] > MAX_JSON_COLLECTION_ITEMS
            or observed[2] > MAX_JSON_INTEGER_DIGITS
        ):
            fail(f"bridge receipt falsely claims no representation excess for {artifact}")

    return AuthenticatedBridgeReceipt(
        receipt_path,
        receipt_bytes,
        receipt,
        receipt_payload_sha,
        profile_sha,
        aggregate_binding["aggregatePayloadSha256"],
        aggregate_binding["inputSetSha256"],
    )


def authenticate_inputs(args: argparse.Namespace) -> AuthenticatedInputs:
    manifest_path = project_path(args.patched_manifest, "--patched-manifest")
    manifest_bytes = read_regular_file(
        manifest_path, "patched result manifest", MAX_MANIFEST_BYTES
    )
    manifest_hash = sha256_bytes(manifest_bytes)
    if manifest_hash != supplied_hex64(
        args.patched_manifest_sha256, "--patched-manifest-sha256"
    ):
        fail("patched result manifest byte hash does not match the supplied hash")
    manifest = parse_json(manifest_bytes, "patched result manifest")
    require_exact_keys(
        manifest,
        {
            "schemaVersion",
            "kind",
            "tool",
            "base",
            "patchManifest",
            "failureEvidence",
            "evaluator",
            "guards",
            "roots",
            "streamsAggregateSha256",
            "resultPayloadHashRule",
            "resultPayloadSha256",
        },
        "patched result manifest",
    )
    if require_int(manifest["schemaVersion"], "schemaVersion") != 1:
        fail("unsupported patched result manifest schemaVersion")
    if manifest["kind"] != "upper-k-historical-path-patch-result":
        fail("unexpected patched result manifest kind")
    if manifest["tool"] != "AgentUpperKHistoricalPatchApplier.py":
        fail("patched result manifest tool identity drifted")
    payload_hash = require_hex64(
        manifest["resultPayloadSha256"], "resultPayloadSha256"
    )
    supplied_payload_hash = supplied_hex64(
        args.patched_manifest_payload_sha256,
        "--patched-manifest-payload-sha256",
    )
    if payload_hash != supplied_payload_hash:
        fail("supplied patched-manifest payload hash does not match the manifest")
    payload = dict(manifest)
    del payload["resultPayloadSha256"]
    if sha256_bytes(canonical_json_bytes(payload)) != payload_hash:
        fail("patched result manifest canonical payload hash drifted")
    if manifest["resultPayloadHashRule"] != (
        "SHA-256 of compact canonical JSON with resultPayloadSha256 omitted"
    ):
        fail("patched result manifest payload-hash rule drifted")

    base = require_dict(manifest["base"], "patched result manifest base")
    expected_base = {
        "manifestFile": BASE_MANIFEST_FILE,
        "manifestByteSha256": BASE_MANIFEST_BYTE_SHA256,
        "aggregateSha256": BASE_AGGREGATE_SHA256,
        "precisionBits": PRECISION_BITS,
    }
    require_exact_json_value(base, expected_base, "patched result manifest base")

    for field, keys in (
        (
            "patchManifest",
            {"file", "byteSha256", "payloadSha256"},
        ),
        (
            "failureEvidence",
            {"file", "byteSha256", "configurationSha256"},
        ),
    ):
        record = require_dict(manifest[field], field)
        require_exact_keys(record, keys, field)
        validate_bare_filename(record["file"], f"{field}.file", ".json")
        for key in keys - {"file"}:
            require_hex64(record[key], f"{field}.{key}")

    guards = require_dict(manifest["guards"], "guards")
    require_exact_keys(guards, PATCH_GUARD_KEYS, "guards")
    for name, value in guards.items():
        if not isinstance(name, str):
            fail("guard names must be strings")
        require_int(value, f"guards.{name}", minimum=1)

    evaluator = validate_evaluator(manifest["evaluator"], args)
    if manifest["failureEvidence"]["configurationSha256"] != (
        evaluator["configurationSha256"]
    ):
        fail("failure evidence and evaluator configuration hashes differ")

    roots_json = require_dict(manifest["roots"], "roots")
    if set(roots_json) != set(ROOT_KEYS):
        fail("patched result manifest must contain exactly the two historical roots")
    roots: dict[str, AuthenticatedRoot] = {}
    for spec in ROOT_SPECS:
        context = f"roots.{spec.key}"
        root_record = require_dict(roots_json[spec.key], context)
        require_exact_keys(
            root_record,
            {
                "root",
                "baseFile",
                "baseByteSha256",
                "baseTopologySha256",
                "baseStatistics",
                "outputFile",
                "output",
                "delta",
                "patches",
            },
            context,
        )
        base_record = BASE_ROOTS[spec.key]
        for field in (
            "root",
            "baseFile",
            "baseByteSha256",
            "baseTopologySha256",
            "baseStatistics",
        ):
            require_exact_json_value(
                root_record[field], base_record[field], f"{context}.{field}"
            )
        output_file = validate_bare_filename(
            root_record["outputFile"], f"{context}.outputFile", ".tree.txt"
        )
        if not output_file.startswith("GeneratedUpperKHistoricalPatched"):
            fail(f"{context}.outputFile lacks the authenticated patched prefix")

        stream_path = project_path(getattr(args, spec.stream_option), f"--{spec.stream_option}")
        if stream_path.name != output_file:
            fail(f"supplied {spec.key} stream basename differs from manifest outputFile")
        file_bytes = read_regular_file(
            stream_path, f"patched {spec.key} stream", MAX_INPUT_BYTES
        )
        supplied_byte = supplied_hex64(
            getattr(args, spec.byte_hash_option), f"--{spec.byte_hash_option}"
        )
        if sha256_bytes(file_bytes) != supplied_byte:
            fail(f"patched {spec.key} byte hash differs from its supplied hash")
        topology = decode_stream(file_bytes, f"patched {spec.key} stream")
        supplied_topology = supplied_hex64(
            getattr(args, spec.topology_hash_option),
            f"--{spec.topology_hash_option}",
        )
        if sha256_text(topology) != supplied_topology:
            fail(f"patched {spec.key} topology hash differs from its supplied hash")
        tree, stats = topology_stats(topology)
        validate_output_record(
            root_record["output"], stats, topology, file_bytes, f"{context}.output"
        )
        if root_record["output"]["byteSha256"] != supplied_byte:
            fail(f"{context}.output byte hash differs from the supplied hash")
        if root_record["output"]["topologySha256"] != supplied_topology:
            fail(f"{context}.output topology hash differs from the supplied hash")

        delta = require_dict(root_record["delta"], f"{context}.delta")
        require_exact_keys(delta, {"nodes", "internal", "leaves", "maxDepth"}, f"{context}.delta")
        for field in ("nodes", "internal", "leaves", "maxDepth"):
            require_int(delta[field], f"{context}.delta.{field}", minimum=0)
            expected_delta = root_record["output"][field] - base_record["baseStatistics"][field]
            if delta[field] != expected_delta:
                fail(f"{context}.delta.{field} is inconsistent")
        if delta["nodes"] != 2 * delta["leaves"] or (
            delta["internal"] != delta["leaves"]
        ):
            fail(f"{context}.delta violates full-binary replacement accounting")
        validate_patch_records(
            root_record["patches"],
            spec.key,
            delta,
            base_record["baseStatistics"]["nodes"],
            base_record["baseStatistics"]["maxDepth"],
        )
        if len(root_record["patches"]) > guards["maxPatchesPerRoot"]:
            fail(f"{context} exceeds its declared patch-count guard")
        for index, patch in enumerate(root_record["patches"]):
            if patch["replacementNodes"] > guards["maxReplacementNodesPerPatch"]:
                fail(
                    f"{context}.patches[{index}] exceeds its declared "
                    "replacement-node guard"
                )
            if patch["replacementMaxExtraDepth"] > guards["maxExtraDepthPerPatch"]:
                fail(
                    f"{context}.patches[{index}] exceeds its declared "
                    "extra-depth guard"
                )
        if root_record["output"]["nodes"] > guards["maxFinalNodesPerRoot"]:
            fail(f"{context}.output exceeds its declared final-node guard")
        if root_record["output"]["maxDepth"] > guards["maxPatchedDepth"]:
            fail(f"{context}.output exceeds its declared patched-depth guard")
        roots[spec.key] = AuthenticatedRoot(
            spec, stream_path, file_bytes, topology, tree, stats, root_record
        )

    if sum(root.stats.nodes for root in roots.values()) > MAX_TOTAL_TOPOLOGY_NODES:
        fail("combined patched topology exceeds the global node guard")
    if sum(root.stats.nodes for root in roots.values()) > guards[
        "maxCombinedFinalNodes"
    ]:
        fail("combined patched topology exceeds its declared manifest guard")
    if sum(
        patch["replacementInternal"]
        for root in roots.values()
        for patch in root.manifest_record["patches"]
    ) > guards["maxTotalAddedInternal"]:
        fail("patched topology exceeds its declared added-internal-node guard")
    if sum(len(root.manifest_record["patches"]) for root in roots.values()) == 0:
        fail("patched result manifest contains no historical leaf replacement")
    output_names = [
        roots[key].manifest_record["outputFile"] for key in ROOT_KEYS
    ]
    if len({name.casefold() for name in output_names}) != len(output_names):
        fail("the two patched stream filenames are not distinct case-insensitively")
    stream_files = {
        roots[key].manifest_record["outputFile"]: roots[key].file_bytes
        for key in ROOT_KEYS
    }
    aggregate = sha256_bytes(
        b"".join(stream_files[name] for name in sorted(stream_files))
    )
    manifest_aggregate = require_hex64(
        manifest["streamsAggregateSha256"], "streamsAggregateSha256"
    )
    supplied_aggregate = supplied_hex64(
        args.streams_aggregate_sha256, "--streams-aggregate-sha256"
    )
    if aggregate != manifest_aggregate or aggregate != supplied_aggregate:
        fail("patched stream aggregate disagrees with its manifest or supplied hash")
    bridge_receipt = authenticate_bridge_receipt(
        args, manifest_path, manifest, evaluator, roots
    )
    return AuthenticatedInputs(
        manifest_path,
        manifest_bytes,
        manifest,
        evaluator,
        roots,
        bridge_receipt,
    )


OPEN_BLOCK = """open LRUpperKHistoricalPackedCertificate
"""


def module_prefix(raw: str) -> str:
    if re.fullmatch(r"Agent[A-Za-z0-9]+", raw) is None:
        fail("--module-prefix must match Agent[A-Za-z0-9]+")
    if len(raw) > 80:
        fail("--module-prefix is too long")
    return raw


def render_config(
    prefix: str,
    args: argparse.Namespace,
    authenticated: AuthenticatedInputs,
    direct_replay_sources: dict[str, object],
) -> tuple[str, str]:
    module = f"{prefix}Config"
    roots = authenticated.roots
    receipt = authenticated.bridge_receipt
    source = f"""import InformationTheory.CourtadeKumar.LRDeterminantUpperKDirectLeafCertificate

/-! Authenticated parameters for the patched historical upper-`K` replay. -/

namespace CourtadeKumar.{GENERATED_NAMESPACE}

def dyadicBits : ℕ := {args.dyadic_bits}
def terms : ℕ := {args.terms}
def sqrtFuel : ℕ := {authenticated.evaluator["parameters"]["sqrtFuel"]}
def logFuel : ℕ := {authenticated.evaluator["parameters"]["logFuel"]}
def bridgeReceiptByteSha256 : String :=
  {json.dumps(sha256_bytes(receipt.file_bytes))}
def bridgeReceiptPayloadSha256 : String :=
  {json.dumps(receipt.payload_sha256)}
def authoritativeProfileSha256 : String :=
  {json.dumps(receipt.profile_sha256)}
def aggregatePayloadSha256 : String :=
  {json.dumps(receipt.aggregate_payload_sha256)}
def aggregateInputSetSha256 : String :=
  {json.dumps(receipt.aggregate_input_set_sha256)}
def patchedManifestByteSha256 : String :=
  {json.dumps(sha256_bytes(authenticated.manifest_bytes))}
def patchedManifestPayloadSha256 : String :=
  {json.dumps(authenticated.manifest["resultPayloadSha256"])}
def evaluatorConfigurationSha256 : String :=
  {json.dumps(authenticated.evaluator["configurationSha256"])}
def evaluatorSourceClosureSha256 : String :=
  {json.dumps(authenticated.evaluator["sourceClosureSha256"])}
def streamsAggregateSha256 : String :=
  {json.dumps(authenticated.manifest["streamsAggregateSha256"])}
def oneToTwoTopologySha256 : String :=
  {json.dumps(sha256_text(roots["oneToTwo"].topology))}
def twoToFourTopologySha256 : String :=
  {json.dumps(sha256_text(roots["twoToFour"].topology))}
def directReplaySourceSetSha256 : String :=
  {json.dumps(direct_replay_sources["sourceSetSha256"])}

end CourtadeKumar.{GENERATED_NAMESPACE}
"""
    return module, source


def render_leaf_group(
    prefix: str,
    config_module: str,
    root: AuthenticatedRoot,
    group_index: int,
    entries: list[tuple[int, PlannedNode]],
    args: argparse.Namespace,
) -> tuple[str, str, dict[PathSteps, tuple[str, str, str]]]:
    stem = root.spec.stem
    module = f"{prefix}{stem}LeavesG{group_index:04d}"
    namespace = f"{stem}LeavesG{group_index:04d}"
    lines = [
        f"import {config_module}",
        "",
        "/-! Three bounded direct checks per authenticated upper-`K` leaf. -/",
        "",
        f"namespace CourtadeKumar.{GENERATED_NAMESPACE}",
        f"namespace {namespace}",
        "",
        OPEN_BLOCK.rstrip(),
        "",
    ]
    references: dict[PathSteps, tuple[str, str, str]] = {}
    for index, planned in entries:
        if not planned.node.is_leaf or planned.node.token != "M":
            fail(f"{module} received a non-leaf arithmetic entry")
        path_name = f"leaf{index:05d}Path"
        box_name = f"leaf{index:05d}Box"
        analytic_name = f"leaf{index:05d}_analyticChecked"
        nodes_name = f"leaf{index:05d}_nodesChecked"
        evaluation_name = f"leaf{index:05d}_evaluationChecked"
        chunk_name = f"leaf{index:05d}"
        lines.extend(
            [
                f"def {path_name} : LRUpperKHistoricalPackedCertificate.Path :=",
                f"  {lean_path(planned.path)}",
                "",
                f"def {box_name} : CertificateBox :=",
                f"  LRUpperKHistoricalPackedCertificate.follow",
                f"    {root.spec.root_lean} {path_name}",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {analytic_name} :",
                f"    LRUpperKDirectLeafCertificate.analyticCheck",
                f"      terms sqrtFuel logFuel {box_name} = true := by",
                "  rfl'",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {nodes_name} :",
                f"    LRUpperKDirectLeafCertificate.nodeCheck",
                f"      dyadicBits terms sqrtFuel logFuel {box_name} = true := by",
                "  rfl'",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {evaluation_name} :",
                f"    LRUpperKDirectLeafCertificate.evaluationCheck",
                f"      dyadicBits terms sqrtFuel logFuel {box_name} = true := by",
                "  rfl'",
                "",
                f"def {chunk_name} :",
                f"    LRUpperKDirectCheckedTree.CheckedAtPath",
                f"      {root.spec.root_lean} {path_name} :=",
                f"  LRUpperKDirectLeafCertificate.checkedTreeOfFactoredChecks",
                f"    dyadicBits terms sqrtFuel logFuel",
                f"    {analytic_name} {nodes_name} {evaluation_name}",
                "",
            ]
        )
        references[planned.path] = (namespace, path_name, chunk_name)
    lines.extend(
        [
            f"end {namespace}",
            f"end CourtadeKumar.{GENERATED_NAMESPACE}",
            "",
        ]
    )
    source = "\n".join(lines)
    if source.count("  rfl'\n") != 3 * len(entries):
        fail(f"{module} did not emit exactly three kernel reductions per leaf")
    return module, source, references


def import_only_source(modules: list[str], purpose: str) -> str:
    if not modules:
        fail(f"cannot build an empty import fan-in for {purpose}")
    return "\n".join(
        [*(f"import {module}" for module in modules), "", f"/-! {purpose} -/", ""]
    )


def add_import_fan_in(
    sources: dict[str, str],
    prefix: str,
    stem: str,
    modules: list[str],
    fan_in: int,
) -> tuple[str, list[str]]:
    if not modules:
        fail(f"empty generated dependency set for {stem}")
    if len(set(modules)) != len(modules):
        fail(f"duplicate generated dependencies for {stem}")
    current = list(modules)
    created: list[str] = []
    level = 0
    while len(current) > 1:
        next_level: list[str] = []
        for index in range(0, len(current), fan_in):
            group = current[index : index + fan_in]
            module = f"{prefix}{stem}ImportL{level:02d}G{index // fan_in:04d}"
            if module in sources:
                fail(f"generated module collision: {module}")
            sources[module] = import_only_source(
                group, f"Bounded import fan-in for {stem}, level {level}."
            )
            created.append(module)
            next_level.append(module)
        current = next_level
        level += 1
    return current[0], created


InternalReference = tuple[str, str]
ChunkReference = tuple[str, str, str]


def render_child_reference(
    child: PlannedNode,
    chunks_by_path: dict[PathSteps, ChunkReference],
    internals_by_path: dict[PathSteps, InternalReference],
) -> list[str]:
    if child.is_chunk:
        namespace, path_name, chunk_name = chunks_by_path[child.path]
        return [
            "(by",
            f"  simpa [{namespace}.{path_name}] using {namespace}.{chunk_name})",
        ]
    namespace, name = internals_by_path[child.path]
    return [f"(by simpa using {namespace}.{name})"]


def render_structural_shard(
    dependency: str,
    root: AuthenticatedRoot,
    module: str,
    namespace: str,
    entries: list[PlannedNode],
    chunks_by_path: dict[PathSteps, ChunkReference],
    internals_by_path: dict[PathSteps, InternalReference],
) -> str:
    lines = [
        f"import {dependency}",
        "",
        "/-! One bounded height-layer shard of proof-preserving joins. -/",
        "",
        f"namespace CourtadeKumar.{GENERATED_NAMESPACE}",
        f"namespace {namespace}",
        "",
        OPEN_BLOCK.rstrip(),
        "",
    ]
    for planned in entries:
        assert planned.lower is not None and planned.upper is not None
        name = internals_by_path[planned.path][1]
        lower = render_child_reference(
            planned.lower, chunks_by_path, internals_by_path
        )
        upper = render_child_reference(
            planned.upper, chunks_by_path, internals_by_path
        )
        lines.extend(
            [
                f"def {name} :",
                f"    LRUpperKDirectCheckedTree.CheckedAtPath",
                f"      {root.spec.root_lean} {lean_path(planned.path)} :=",
                f"  LRUpperKDirectCheckedTree.joinAtPath",
                f"    (ancestor := {root.spec.root_lean})",
                f"    {lean_path(planned.path)}",
                f"    {lean_axis(planned.node.token)}",
            ]
        )
        lines.extend("    " + line for line in lower)
        lines.extend("    " + line for line in upper)
        lines.append("")
    lines.extend(
        [
            f"end {namespace}",
            f"end CourtadeKumar.{GENERATED_NAMESPACE}",
            "",
        ]
    )
    return "\n".join(lines)


def render_root_final(
    dependency: str,
    root: AuthenticatedRoot,
    prefix: str,
    plan: PlannedNode,
    chunks_by_path: dict[PathSteps, ChunkReference],
    internals_by_path: dict[PathSteps, InternalReference],
) -> tuple[str, str]:
    module = f"{prefix}{root.spec.stem}CheckedTree"
    namespace = f"{root.spec.stem}Assembly"
    if plan.is_chunk:
        chunk_namespace, path_name, chunk_name = chunks_by_path[plan.path]
        reference = [
            "(by",
            f"  simpa [{chunk_namespace}.{path_name}] using",
            f"    {chunk_namespace}.{chunk_name})",
        ]
    else:
        child_namespace, child_name = internals_by_path[plan.path]
        reference = [
            f"(by simpa using {child_namespace}.{child_name})",
        ]
    lines = [
        f"import {dependency}",
        "",
        "/-! The structurally reassembled checked tree at one historical root. -/",
        "",
        f"namespace CourtadeKumar.{GENERATED_NAMESPACE}",
        f"namespace {namespace}",
        "",
        OPEN_BLOCK.rstrip(),
        "",
        "def checkedTree :",
        f"    LRUpperKDirectCheckedTree.CheckedTree {root.spec.root_lean} :=",
        "  LRUpperKDirectCheckedTree.checkedTreeOfEmptyPath",
    ]
    lines.extend("    " + line for line in reference)
    lines.extend(
        [
            "",
            f"end {namespace}",
            f"end CourtadeKumar.{GENERATED_NAMESPACE}",
            "",
        ]
    )
    return module, "\n".join(lines)


def render_final_assembly(
    prefix: str, one_module: str, two_module: str
) -> tuple[str, str]:
    module = f"{prefix}Assembly"
    source = f"""import {one_module}
import {two_module}

/-! Final theorem-level join of the separately rooted patched upper-`K` trees. -/

namespace CourtadeKumar

theorem {FINAL_THEOREM} :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion :=
  LRUpperKDirectCheckedTree.upperKRegionCertificate_of_twoCheckedTrees
    {GENERATED_NAMESPACE}.OneToTwoAssembly.checkedTree
    {GENERATED_NAMESPACE}.TwoToFourAssembly.checkedTree

end CourtadeKumar
"""
    return module, source


def chunks_in_groups(
    entries: list[PlannedNode], size: int
) -> list[list[tuple[int, PlannedNode]]]:
    indexed = list(enumerate(entries))
    return [indexed[index : index + size] for index in range(0, len(indexed), size)]


def validate_generated_graph(sources: dict[str, str], prefix: str) -> None:
    dependency_pattern = re.compile(r"^import\s+(\S+)\s*$", re.MULTILINE)
    graph: dict[str, list[str]] = {}
    for module, source in sources.items():
        dependencies = [
            dependency
            for dependency in dependency_pattern.findall(source)
            if dependency.startswith(prefix)
        ]
        missing = [dependency for dependency in dependencies if dependency not in sources]
        if missing:
            fail(f"{module} imports missing generated modules: {missing}")
        graph[module] = dependencies

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            fail(f"generated import cycle reaches {module}")
        if module in visited:
            return
        visiting.add(module)
        for dependency in graph[module]:
            visit(dependency)
        visiting.remove(module)
        visited.add(module)

    for module in sorted(graph):
        visit(module)


def validate_rendered(
    sources: dict[str, str], prefix: str, total_chunks: int
) -> None:
    if len(sources) > MAX_GENERATED_MODULES:
        fail("generated Lean module count exceeds the global guard")
    combined_bytes = sum(len(source.encode("utf-8")) for source in sources.values())
    if combined_bytes > MAX_GENERATED_SOURCE_BYTES:
        fail("generated Lean source exceeds the global byte guard")
    combined = "\n".join(sources.values())
    for forbidden in FORBIDDEN_LEAN:
        if forbidden in combined:
            fail(f"generated Lean contains forbidden text {forbidden!r}")
    if combined.count("  rfl'\n") != 3 * total_chunks:
        fail("generated replay does not contain exactly three rfl' checks per leaf")
    expected_leaf_uses = {
        "LRUpperKDirectLeafCertificate.analyticCheck": total_chunks,
        "LRUpperKDirectLeafCertificate.nodeCheck": total_chunks,
        "LRUpperKDirectLeafCertificate.evaluationCheck": total_chunks,
        "LRUpperKDirectLeafCertificate.checkedTreeOfFactoredChecks": total_chunks,
    }
    for needle, expected in expected_leaf_uses.items():
        if combined.count(needle) != expected:
            fail(
                f"generated replay contains {combined.count(needle)} uses of "
                f"{needle}, expected {expected}"
            )
    for legacy in ("packedCheck", "PackedCheckedChunk"):
        if legacy in combined:
            fail(f"generated replay contains legacy proof shape {legacy}")
    if combined.count(f"theorem {FINAL_THEOREM}") != 1:
        fail("generated replay does not export exactly one final theorem")
    validate_generated_graph(sources, prefix)


def build(
    args: argparse.Namespace, authenticated: AuthenticatedInputs
) -> tuple[dict[str, str], dict[str, object]]:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("generator source changed during the authenticated planning pass")
    prefix = module_prefix(args.module_prefix)
    direct_replay_sources = bind_direct_replay_sources()
    config_module, config_source = render_config(
        prefix, args, authenticated, direct_replay_sources
    )
    sources: dict[str, str] = {config_module: config_source}
    root_manifests: list[dict[str, object]] = []
    root_final_modules: dict[str, str] = {}
    total_chunks = 0
    total_structural_nodes = 0

    for spec in ROOT_SPECS:
        root = authenticated.roots[spec.key]
        plan = make_plan(root.tree, args.max_chunk_leaves)
        if reconstruct(plan) != root.topology:
            fail(f"{spec.key} frontier does not reconstruct its authenticated stream")
        frontier_nodes = list(frontier(plan))
        if any(leaf_count(item.node) > args.max_chunk_leaves for item in frontier_nodes):
            fail(f"{spec.key} contains an oversized arithmetic chunk")
        if len({item.path for item in frontier_nodes}) != len(frontier_nodes):
            fail(f"{spec.key} frontier paths are not unique")
        total_chunks += len(frontier_nodes)

        leaf_modules: list[str] = []
        chunk_references: dict[PathSteps, ChunkReference] = {}
        chunk_records: list[dict[str, object]] = []
        groups = chunks_in_groups(frontier_nodes, args.chunks_per_module)
        for group_index, group in enumerate(groups):
            module, source, references = render_leaf_group(
                prefix, config_module, root, group_index, group, args
            )
            if module in sources:
                fail(f"generated module collision: {module}")
            sources[module] = source
            leaf_modules.append(module)
            for path, reference in references.items():
                if path in chunk_references:
                    fail(f"duplicate chunk reference in {spec.key}: {path_text(path)}")
                chunk_references[path] = reference
            for index, planned in group:
                packed = planned.node.packed()
                chunk_records.append(
                    {
                        "index": index,
                        "module": module,
                        "path": path_text(planned.path),
                        "pathSteps": [
                            {"axis": step.axis, "branch": step.branch}
                            for step in planned.path
                        ],
                        "bounds": bounds_at(spec, planned.path),
                        "packed": packed,
                        "packedSha256": sha256_text(packed),
                        "bytes": len(packed),
                        "nodes": node_count(planned.node),
                        "leaves": leaf_count(planned.node),
                        "maxDepth": max_depth(planned.node),
                    }
                )
        if len(chunk_references) != len(frontier_nodes):
            fail(f"{spec.key} lost a frontier chunk reference")

        coverage, leaf_indexes = add_import_fan_in(
            sources,
            prefix,
            f"{spec.stem}LeafCoverage",
            leaf_modules,
            args.max_imports_per_index,
        )
        layer_map = nodes_by_level(plan)
        structural_expected = structural_node_count(plan)
        if sum(len(entries) for entries in layer_map.values()) != structural_expected:
            fail(f"{spec.key} structural layer accounting drifted")
        total_structural_nodes += structural_expected
        internal_references: dict[PathSteps, InternalReference] = {}
        layer_records: list[dict[str, object]] = []
        all_index_modules = list(leaf_indexes)

        for level in sorted(layer_map):
            entries = layer_map[level]
            shards = [
                entries[index : index + args.structural_defs_per_module]
                for index in range(0, len(entries), args.structural_defs_per_module)
            ]
            shard_metadata: list[tuple[str, str, list[PlannedNode]]] = []
            layer_node_records: list[dict[str, object]] = []
            for shard_index, shard in enumerate(shards):
                module = f"{prefix}{spec.stem}Layer{level:02d}S{shard_index:04d}"
                namespace = f"{spec.stem}Layer{level:02d}S{shard_index:04d}"
                for planned in shard:
                    if planned.path in internal_references:
                        fail(f"duplicate structural path in {spec.key}")
                    internal_references[planned.path] = (
                        namespace,
                        f"node_{path_identifier(planned.path)}",
                    )
                    layer_node_records.append(
                        {
                            "path": path_text(planned.path),
                            "axis": planned.node.token,
                            "module": module,
                        }
                    )
                shard_metadata.append((module, namespace, shard))
            shard_modules: list[str] = []
            for module, namespace, shard in shard_metadata:
                source = render_structural_shard(
                    coverage,
                    root,
                    module,
                    namespace,
                    shard,
                    chunk_references,
                    internal_references,
                )
                if module in sources:
                    fail(f"generated module collision: {module}")
                sources[module] = source
                shard_modules.append(module)
            previous_coverage = coverage
            coverage, layer_indexes = add_import_fan_in(
                sources,
                prefix,
                f"{spec.stem}Layer{level:02d}Coverage",
                [previous_coverage, *shard_modules],
                args.max_imports_per_index,
            )
            all_index_modules.extend(layer_indexes)
            layer_records.append(
                {
                    "level": level,
                    "nodeCount": len(entries),
                    "inputCoverageModule": previous_coverage,
                    "shardModules": shard_modules,
                    "outputCoverageModule": coverage,
                    "nodes": layer_node_records,
                }
            )

        if len(internal_references) != structural_expected:
            fail(f"{spec.key} lost a structural node reference")
        root_module, root_source = render_root_final(
            coverage,
            root,
            prefix,
            plan,
            chunk_references,
            internal_references,
        )
        if root_module in sources:
            fail(f"generated module collision: {root_module}")
        sources[root_module] = root_source
        root_final_modules[spec.key] = root_module

        root_manifests.append(
            {
                "key": spec.key,
                "rootLean": spec.root_lean,
                "input": relative_project_path(root.path),
                "inputByteSha256": sha256_bytes(root.file_bytes),
                "inputTopologySha256": sha256_text(root.topology),
                "nodes": root.stats.nodes,
                "internal": root.stats.internal,
                "leaves": root.stats.leaves,
                "maxDepth": root.stats.max_depth,
                "splitS": root.stats.split_s,
                "splitK": root.stats.split_k,
                "splitH": root.stats.split_h,
                "frontierReconstructionSha256": sha256_text(reconstruct(plan)),
                "chunkCount": len(frontier_nodes),
                "leafGroupModules": leaf_modules,
                "leafImportIndexModules": leaf_indexes,
                "structuralNodeCount": structural_expected,
                "structuralLayerCount": len(layer_map),
                "structuralLayers": layer_records,
                "allStructuralImportIndexModules": all_index_modules,
                "checkedTreeModule": root_module,
                "chunks": chunk_records,
            }
        )

    final_module, final_source = render_final_assembly(
        prefix,
        root_final_modules["oneToTwo"],
        root_final_modules["twoToFour"],
    )
    if final_module in sources:
        fail(f"generated module collision: {final_module}")
    sources[final_module] = final_source
    validate_rendered(sources, prefix, total_chunks)

    output_hashes = {
        f"{module}.lean": sha256_bytes(source.encode("utf-8"))
        for module, source in sorted(sources.items())
    }
    manifest_core: dict[str, object] = {
        "format": "authenticated patched upper-K direct-leaf Lean replay plan v3",
        "alphabet": "Mskh",
        "generator": SCRIPT.name,
        "generatorSha256": SCRIPT_BYTE_SHA256,
        "proofAuthority": PROOF_AUTHORITY,
        "directReplayImplementation": direct_replay_sources,
        "authenticatedInputs": {
            "bridgeReceipt": {
                "file": relative_project_path(authenticated.bridge_receipt.path),
                "byteSha256": sha256_bytes(authenticated.bridge_receipt.file_bytes),
                "payloadSha256": authenticated.bridge_receipt.payload_sha256,
                "profileSha256": authenticated.bridge_receipt.profile_sha256,
                "aggregatePayloadSha256": (
                    authenticated.bridge_receipt.aggregate_payload_sha256
                ),
                "aggregateInputSetSha256": (
                    authenticated.bridge_receipt.aggregate_input_set_sha256
                ),
            },
            "patchedManifest": relative_project_path(authenticated.manifest_path),
            "patchedManifestByteSha256": sha256_bytes(authenticated.manifest_bytes),
            "patchedManifestPayloadSha256": authenticated.manifest[
                "resultPayloadSha256"
            ],
            "streamsAggregateSha256": authenticated.manifest[
                "streamsAggregateSha256"
            ],
            "evaluator": authenticated.evaluator,
        },
        "parameters": {
            "dyadicBits": args.dyadic_bits,
            "terms": args.terms,
            "maxChunkLeaves": args.max_chunk_leaves,
            "chunksPerModule": args.chunks_per_module,
            "structuralDefinitionsPerModule": args.structural_defs_per_module,
            "maxImportsPerIndex": args.max_imports_per_index,
            "maxRecDepth": args.max_rec_depth,
            "maxHeartbeats": args.max_heartbeats,
            "modulePrefix": prefix,
        },
        "outputDirectory": relative_project_path(args.validated_output_dir),
        "rootCount": 2,
        "totalChunks": total_chunks,
        "totalKernelReductions": 3 * total_chunks,
        "totalStructuralNodes": total_structural_nodes,
        "leanModuleCount": len(sources),
        "roots": root_manifests,
        "outputs": output_hashes,
        "finalModule": final_module,
        "finalTheorem": f"CourtadeKumar.{FINAL_THEOREM}",
    }
    plan_hash = sha256_bytes(canonical_json_bytes(manifest_core))
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("generator source changed while the replay plan was rendered")
    if bind_direct_replay_sources() != direct_replay_sources:
        fail("direct replay Lean implementation changed while the plan was rendered")
    return sources, {**manifest_core, "planSha256": plan_hash}


def summary(manifest: dict[str, object]) -> dict[str, object]:
    return {
        "status": "validated-read-only",
        "planSha256": manifest["planSha256"],
        "bridgeReceiptPayloadSha256": manifest["authenticatedInputs"][
            "bridgeReceipt"
        ]["payloadSha256"],
        "directReplaySourceSetSha256": manifest["directReplayImplementation"][
            "sourceSetSha256"
        ],
        "outputDirectory": manifest["outputDirectory"],
        "totalChunks": manifest["totalChunks"],
        "totalKernelReductions": manifest["totalKernelReductions"],
        "totalStructuralNodes": manifest["totalStructuralNodes"],
        "leanModuleCount": manifest["leanModuleCount"],
        "finalModule": manifest["finalModule"],
        "finalTheorem": manifest["finalTheorem"],
        "roots": [
            {
                "key": root["key"],
                "nodes": root["nodes"],
                "leaves": root["leaves"],
                "chunks": root["chunkCount"],
                "structuralNodes": root["structuralNodeCount"],
                "structuralLayers": root["structuralLayerCount"],
                "checkedTreeModule": root["checkedTreeModule"],
            }
            for root in manifest["roots"]
        ],
    }


def validate_positive_arguments(args: argparse.Namespace) -> None:
    values = {
        "dyadic_bits": args.dyadic_bits,
        "terms": args.terms,
        "max_chunk_leaves": args.max_chunk_leaves,
        "chunks_per_module": args.chunks_per_module,
        "structural_defs_per_module": args.structural_defs_per_module,
        "max_imports_per_index": args.max_imports_per_index,
        "max_rec_depth": args.max_rec_depth,
    }
    invalid = {name: value for name, value in values.items() if value <= 0}
    if invalid:
        fail(f"arguments must be positive: {invalid}")
    if args.max_heartbeats < 0:
        fail("--max-heartbeats must be nonnegative")
    if not 8 <= args.dyadic_bits <= 128:
        fail("--dyadic-bits must lie in [8,128]")
    if args.max_chunk_leaves != 1:
        fail("direct-leaf replay requires --max-chunk-leaves=1")
    if not 1 <= args.chunks_per_module <= 8:
        fail("--chunks-per-module must lie in the tested range [1,8]")
    if args.structural_defs_per_module > 512:
        fail("--structural-defs-per-module exceeds the hard guard 512")
    if not 2 <= args.max_imports_per_index <= 128:
        fail("--max-imports-per-index must lie in [2,128]")
    module_prefix(args.module_prefix)


def add_common_arguments(command: argparse.ArgumentParser) -> None:
    command.add_argument("--bridge-receipt", required=True)
    command.add_argument("--bridge-receipt-sha256", required=True)
    command.add_argument("--bridge-receipt-payload-sha256", required=True)
    command.add_argument("--patched-manifest", required=True)
    command.add_argument("--patched-manifest-sha256", required=True)
    command.add_argument("--patched-manifest-payload-sha256", required=True)
    command.add_argument("--one-to-two-stream", required=True)
    command.add_argument("--one-to-two-byte-sha256", required=True)
    command.add_argument("--one-to-two-topology-sha256", required=True)
    command.add_argument("--two-to-four-stream", required=True)
    command.add_argument("--two-to-four-byte-sha256", required=True)
    command.add_argument("--two-to-four-topology-sha256", required=True)
    command.add_argument("--streams-aggregate-sha256", required=True)
    command.add_argument("--evaluator-configuration-sha256", required=True)
    command.add_argument("--evaluator-source-closure-sha256", required=True)
    command.add_argument("--output-dir", required=True)
    command.add_argument("--dyadic-bits", type=int, default=24)
    command.add_argument("--terms", type=int, default=12)
    command.add_argument("--max-chunk-leaves", type=int, default=1)
    command.add_argument("--chunks-per-module", type=int, default=8)
    command.add_argument("--structural-defs-per-module", type=int, default=128)
    command.add_argument("--max-imports-per-index", type=int, default=64)
    command.add_argument("--max-rec-depth", type=int, default=1000000)
    command.add_argument("--max-heartbeats", type=int, default=0)
    command.add_argument(
        "--module-prefix", default="AgentUpperKHistoricalPatchedReplayGenerated"
    )


def prepared(args: argparse.Namespace) -> tuple[AuthenticatedInputs, dict[str, str], dict[str, object]]:
    validate_repository_location()
    validate_positive_arguments(args)
    (
        args.validated_output_dir,
        args.validated_output_identity,
    ) = output_directory(args.output_dir)
    authenticated = authenticate_inputs(args)
    sources, manifest = build(args, authenticated)
    return authenticated, sources, manifest


def command_plan(args: argparse.Namespace) -> None:
    _authenticated, _sources, manifest = prepared(args)
    print(json.dumps(summary(manifest), indent=2, sort_keys=True))


def exclusive_create_all(
    directory: Path,
    expected_directory_identity: tuple[int, int],
    outputs: dict[Path, bytes],
) -> None:
    if not outputs:
        fail("refusing an empty generated-output transaction")
    if any(path.parent != directory for path in outputs):
        fail("generated-output transaction escaped its pinned directory")
    descriptors: dict[Path, int] = {}
    identities: dict[Path, tuple[int, int]] = {}
    created: list[Path] = []
    directory_flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        directory_flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        directory_flags |= os.O_NOFOLLOW
    try:
        directory_descriptor = os.open(directory, directory_flags)
    except OSError as error:
        fail(f"cannot pin --output-dir for emission: {error}")
    try:
        directory_metadata = os.fstat(directory_descriptor)
        if not stat.S_ISDIR(directory_metadata.st_mode) or (
            directory_metadata.st_dev,
            directory_metadata.st_ino,
        ) != expected_directory_identity:
            fail("--output-dir identity changed after validation")
        file_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
        if hasattr(os, "O_NOFOLLOW"):
            file_flags |= os.O_NOFOLLOW
        try:
            for path in sorted(outputs, key=lambda item: item.name):
                descriptor = os.open(
                    path.name,
                    file_flags,
                    0o644,
                    dir_fd=directory_descriptor,
                )
                descriptors[path] = descriptor
                metadata = os.fstat(descriptor)
                identities[path] = (metadata.st_dev, metadata.st_ino)
                created.append(path)
            for path in sorted(outputs, key=lambda item: item.name):
                descriptor = descriptors.pop(path)
                with os.fdopen(descriptor, "wb", closefd=True) as handle:
                    handle.write(outputs[path])
                    handle.flush()
                    os.fsync(handle.fileno())
            os.fsync(directory_descriptor)
        except BaseException:
            for descriptor in descriptors.values():
                try:
                    os.close(descriptor)
                except OSError:
                    pass
            for path in created:
                try:
                    metadata = os.stat(
                        path.name,
                        dir_fd=directory_descriptor,
                        follow_symlinks=False,
                    )
                    if stat.S_ISREG(metadata.st_mode) and (
                        metadata.st_dev,
                        metadata.st_ino,
                    ) == identities[path]:
                        os.unlink(path.name, dir_fd=directory_descriptor)
                except (FileNotFoundError, OSError):
                    pass
            raise
    finally:
        os.close(directory_descriptor)


def command_generate(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        fail("refusing emission without --confirm-write")
    _authenticated, sources, manifest = prepared(args)
    expected_plan = supplied_hex64(args.expected_plan_sha256, "--expected-plan-sha256")
    if expected_plan != manifest["planSha256"]:
        fail("--expected-plan-sha256 differs from the freshly authenticated plan")
    directory: Path = args.validated_output_dir
    output_manifest_name = f"{module_prefix(args.module_prefix)}Manifest.json"
    rendered_manifest = pretty_json_bytes(manifest)
    outputs: dict[Path, bytes] = {
        safe_output_path(directory, f"{module}.lean"): source.encode("utf-8")
        for module, source in sources.items()
    }
    manifest_path = safe_output_path(directory, output_manifest_name)
    if manifest_path in outputs:
        fail("generated plan manifest collided with a Lean module")
    outputs[manifest_path] = rendered_manifest
    if any(path.exists() or path.is_symlink() for path in outputs):
        collisions = sorted(path.name for path in outputs if path.exists() or path.is_symlink())
        fail(f"refusing to overwrite generated outputs: {collisions}")
    exclusive_create_all(
        directory,
        args.validated_output_identity,
        outputs,
    )
    written = summary(manifest)
    written["status"] = "written"
    written["writtenFiles"] = len(outputs)
    written["planManifest"] = output_manifest_name
    print(json.dumps(written, sort_keys=True))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="authenticate and plan without writing")
    add_common_arguments(plan)
    plan.set_defaults(handler=command_plan)
    generate = commands.add_parser(
        "generate", help="emit exclusively into the supplied scratch output directory"
    )
    add_common_arguments(generate)
    generate.add_argument("--expected-plan-sha256", required=True)
    generate.add_argument("--confirm-write", action="store_true")
    generate.set_defaults(handler=command_generate)
    return result


def main(argv: Iterable[str] | None = None) -> None:
    args = parser().parse_args(list(argv) if argv is not None else None)
    args.handler(args)


if __name__ == "__main__":
    try:
        main()
    except ReplayPlanError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
