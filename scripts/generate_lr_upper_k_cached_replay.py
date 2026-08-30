#!/usr/bin/env python3
"""Plan or emit the authenticated scalar-cached patched upper-``K`` replay.

This generator reauthenticates the historical bridge receipt and patched
topologies through the direct replay generator, authenticates a complete
scalar-cache proof manifest and all of its generated Lean source bytes, and
then emits semantic checked leaves.  High-multiplicity scalar calls reference
their shared kernel-authenticated cache theorems.  Every other scalar remains
an exact ``outerEnclosure`` expression with the generic cover theorem.

Each leaf kernel-checks its literal box against the authenticated path, the
center/whole scalar-argument records, the analytic predicate, node positivity,
and midpoint evaluation.  Structural assembly reuses the existing semantic
height-layer joins and never repeats leaf arithmetic.  Python output has no
proof authority.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable

import generate_lr_upper_k_scalar_cache_proofs as cache_proofs


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
replay = cache_proofs.collection.query_plan.replay
query_plan = cache_proofs.collection.query_plan
FORMAT = "authenticated patched upper-K scalar-cached Lean replay plan v1"
PROOF_AUTHORITY = (
    "ordinary Lean reductions for cache literals, leaf geometry, analytic "
    "checks, node checks, and midpoint checks, plus proved semantic joins"
)
GENERATED_NAMESPACE = "LRUpperKHistoricalPatchedCachedReplayGenerated"
FINAL_THEOREM = "lrDeterminantUpperKRegion_historicalPatched_cached_proved"
CACHED_REPLAY_ADAPTER_FILES = (
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKCachedScalarArguments.lean",
)


@dataclass(frozen=True, slots=True)
class CacheReference:
    cache_id: str
    kind: str
    s: Fraction
    y: Fraction
    module: str
    namespace: str
    value_name: str
    covers_name: str

    @property
    def qualified_value(self) -> str:
        return (
            f"CourtadeKumar.{cache_proofs.GENERATED_NAMESPACE}."
            f"{self.namespace}.{self.value_name}"
        )

    @property
    def qualified_covers(self) -> str:
        return (
            f"CourtadeKumar.{cache_proofs.GENERATED_NAMESPACE}."
            f"{self.namespace}.{self.covers_name}"
        )


@dataclass(frozen=True, slots=True)
class AuthenticatedCache:
    path: Path
    file_bytes: bytes
    manifest: dict[str, Any]
    source_dir: Path
    coverage_module: str
    entries: dict[str, CacheReference]
    query_manifest: dict[str, Any]


def fail(message: str) -> None:
    raise replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return cache_proofs.canonical_json_bytes(value)


def pretty_json_bytes(value: object) -> bytes:
    return cache_proofs.pretty_json_bytes(value)


def fraction_from_record(value: object, context: str) -> Fraction:
    return cache_proofs.fraction_from_record(value, context)


def fraction_text(value: Fraction) -> str:
    return cache_proofs.fraction_text(value)


def bind_cached_replay_adapter_sources() -> dict[str, object]:
    records: list[dict[str, object]] = []
    for relative in CACHED_REPLAY_ADAPTER_FILES:
        path = replay.project_path(relative, f"cached replay adapter {relative}")
        data = replay.read_regular_file(
            path, f"cached replay adapter {relative}", replay.MAX_INPUT_BYTES
        )
        records.append(
            {"file": relative, "bytes": len(data), "byteSha256": sha256_bytes(data)}
        )
    core: dict[str, object] = {
        "algorithm": replay.DIRECT_REPLAY_SOURCE_SET_ALGORITHM,
        "files": records,
    }
    return {**core, "sourceSetSha256": sha256_bytes(canonical_json_bytes(core))}


def validate_query_matches_inputs(
    query: dict[str, Any], authenticated: replay.AuthenticatedInputs
) -> None:
    inputs = query.get("authenticatedInputs")
    if not isinstance(inputs, dict):
        fail("cache query manifest lacks authenticated inputs")
    receipt = authenticated.bridge_receipt
    expected_roots = {
        key: {
            "byteSha256": sha256_bytes(root.file_bytes),
            "topologySha256": replay.sha256_text(root.topology),
            "leaves": root.stats.leaves,
        }
        for key, root in authenticated.roots.items()
    }
    expected = {
        "bridgeReceiptFile": replay.relative_project_path(receipt.path),
        "bridgeReceiptByteSha256": sha256_bytes(receipt.file_bytes),
        "bridgeReceiptPayloadSha256": receipt.payload_sha256,
        "authoritativeProfileSha256": receipt.profile_sha256,
        "patchedManifestFile": replay.relative_project_path(
            authenticated.manifest_path
        ),
        "patchedManifestByteSha256": sha256_bytes(authenticated.manifest_bytes),
        "patchedManifestPayloadSha256": authenticated.manifest[
            "resultPayloadSha256"
        ],
        "streamsAggregateSha256": authenticated.manifest[
            "streamsAggregateSha256"
        ],
        "roots": expected_roots,
    }
    if inputs != expected:
        fail("cache query manifest authenticates different replay inputs")


def authenticate_cache(
    args: argparse.Namespace, authenticated: replay.AuthenticatedInputs
) -> AuthenticatedCache:
    path = replay.project_path(args.cache_proof_manifest, "--cache-proof-manifest")
    data = replay.read_regular_file(
        path, "scalar-cache proof manifest", 64 * 1024 * 1024
    )
    if sha256_bytes(data) != replay.supplied_hex64(
        args.cache_proof_manifest_sha256, "--cache-proof-manifest-sha256"
    ):
        fail("scalar-cache proof manifest byte hash differs from the supplied hash")
    try:
        manifest = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse scalar-cache proof manifest: {error}")
    if not isinstance(manifest, dict):
        fail("scalar-cache proof manifest must be a JSON object")
    plan_sha = manifest.get("planSha256")
    supplied_plan = replay.supplied_hex64(
        args.cache_proof_plan_sha256, "--cache-proof-plan-sha256"
    )
    if plan_sha != supplied_plan:
        fail("scalar-cache proof plan hash differs from the supplied hash")
    core = dict(manifest)
    if "planSha256" not in core:
        fail("scalar-cache proof manifest lacks planSha256")
    del core["planSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != plan_sha:
        fail("scalar-cache proof plan hash does not authenticate its content")
    if manifest.get("format") != cache_proofs.FORMAT:
        fail("scalar-cache proof manifest format drifted")
    if manifest.get("generator") != {
        "file": cache_proofs.SCRIPT.name,
        "byteSha256": cache_proofs.SCRIPT_BYTE_SHA256,
    }:
        fail("scalar-cache proof manifest generator binding drifted")
    implementation = manifest.get("implementation")
    if implementation != {
        "directReplay": replay.bind_direct_replay_sources(),
        "cachedOverlay": query_plan.bind_cache_overlay_sources(),
    }:
        fail("scalar-cache proof implementation binding is stale")

    source_dir = path.parent
    if manifest.get("outputDirectory") != replay.relative_project_path(source_dir):
        fail("scalar-cache proof source directory differs from its manifest")
    outputs = manifest.get("outputs")
    if not isinstance(outputs, dict) or len(outputs) != manifest.get(
        "leanModuleCount"
    ):
        fail("scalar-cache proof output table is malformed")
    for filename, expected_hash in outputs.items():
        if (
            not isinstance(filename, str)
            or Path(filename).name != filename
            or not filename.endswith(".lean")
            or not isinstance(expected_hash, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected_hash) is None
        ):
            fail("scalar-cache proof output record is invalid")
        source = source_dir / filename
        source_bytes = replay.read_regular_file(
            source, f"scalar-cache proof source {filename}", 2 * 1024 * 1024
        )
        if sha256_bytes(source_bytes) != expected_hash:
            fail(f"scalar-cache proof source hash drifted for {filename}")
        for forbidden in replay.FORBIDDEN_LEAN:
            if forbidden in source_bytes.decode("utf-8"):
                fail(f"scalar-cache proof source {filename} contains {forbidden!r}")

    query_record = manifest.get("queryManifest")
    if not isinstance(query_record, dict):
        fail("scalar-cache proof manifest lacks its query binding")
    query_path = replay.project_path(query_record.get("file"), "cache query manifest")
    query_dir = query_path.parent
    query_bytes = replay.read_regular_file(
        query_path, "cache query manifest", cache_proofs.collection.MAX_MANIFEST_BYTES
    )
    if query_record != {
        "file": replay.relative_project_path(query_path),
        "byteSha256": sha256_bytes(query_bytes),
        "planSha256": query_record.get("planSha256"),
    }:
        fail("scalar-cache proof query byte binding is malformed")
    query = cache_proofs.collection.strict_manifest(query_path, query_dir)
    if query["planSha256"] != query_record["planSha256"]:
        fail("scalar-cache proof query plan binding drifted")
    validate_query_matches_inputs(query, authenticated)
    qparams = query["parameters"]
    if (
        qparams["dyadicBits"] != args.dyadic_bits
        or qparams["terms"] != args.terms
        or qparams["sqrtFuel"]
        != authenticated.evaluator["parameters"]["sqrtFuel"]
        or qparams["logFuel"] != authenticated.evaluator["parameters"]["logFuel"]
    ):
        fail("scalar-cache proof parameters differ from the replay parameters")

    records = manifest.get("entries")
    if not isinstance(records, list) or len(records) != manifest.get("entryCount"):
        fail("scalar-cache proof entry table is malformed")
    entries: dict[str, CacheReference] = {}
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            fail(f"cache proof entry {index} is not an object")
        identifier = record.get("cacheId")
        kind = record.get("kind")
        if (
            not isinstance(identifier, str)
            or re.fullmatch(r"[0-9a-f]{64}", identifier) is None
            or kind not in ("a", "c")
        ):
            fail(f"cache proof entry {index} has an invalid key")
        if identifier in entries:
            fail("scalar-cache proof entry IDs are not unique")
        s = fraction_from_record(record.get("s"), f"cache entry {index}.s")
        y = fraction_from_record(record.get("y"), f"cache entry {index}.y")
        expected_id = query_plan.cache_id(
            query_plan.ScalarKey(kind, s, y),
            argparse.Namespace(
                dyadic_bits=qparams["dyadicBits"],
                terms=qparams["terms"],
                authenticated_sqrt_fuel=qparams["sqrtFuel"],
                authenticated_log_fuel=qparams["logFuel"],
            ),
        )
        if expected_id != identifier:
            fail(f"cache proof entry {index} ID does not hash its exact key")
        module = record.get("module")
        namespace = record.get("namespace")
        value_name = record.get("valueName")
        covers_name = record.get("coversName")
        for name, value in (
            ("module", module),
            ("namespace", namespace),
            ("valueName", value_name),
            ("coversName", covers_name),
        ):
            if not isinstance(value, str) or re.fullmatch(r"[A-Za-z0-9_]+", value) is None:
                fail(f"cache proof entry {index} has invalid {name}")
        if f"{module}.lean" not in outputs:
            fail(f"cache proof entry {index} references an unknown module")
        entries[identifier] = CacheReference(
            identifier, kind, s, y, module, namespace, value_name, covers_name
        )
    if len(entries) != query["selectedScalarKeys"]:
        fail("scalar-cache proof entries do not cover every selected query key")
    coverage = manifest.get("coverageModule")
    if not isinstance(coverage, str) or f"{coverage}.lean" not in outputs:
        fail("scalar-cache proof coverage module is missing")
    return AuthenticatedCache(
        path, data, manifest, source_dir, coverage, entries, query
    )


def cached_replay_prefix(raw: str) -> str:
    return replay.module_prefix(raw)


def box_lean(box: query_plan.ExactBox) -> str:
    return (
        "{ sLo := "
        + fraction_text(box.s_lo)
        + ", sHi := "
        + fraction_text(box.s_hi)
        + ", kLo := "
        + fraction_text(box.k_lo)
        + ", kHi := "
        + fraction_text(box.k_hi)
        + ", chiLo := "
        + fraction_text(box.h_lo)
        + ", chiHi := "
        + fraction_text(box.h_hi)
        + " }"
    )


def cache_key_id(key: query_plan.ScalarKey, args: argparse.Namespace) -> str:
    return query_plan.cache_id(key, args)


def scalar_exact(key: query_plan.ScalarKey) -> str:
    scalar = "aAutoI" if key.kind == "a" else "cAutoI"
    return (
        f"LRUpperKHistoricalACValues.{scalar} terms sqrtFuel logFuel "
        f"({fraction_text(key.s)}) ({fraction_text(key.y)})"
    )


def scalar_value_expression(
    key: query_plan.ScalarKey,
    args: argparse.Namespace,
    cache: AuthenticatedCache,
) -> tuple[str, CacheReference | None]:
    identifier = cache_key_id(key, args)
    reference = cache.entries.get(identifier)
    if reference is not None:
        if (reference.kind, reference.s, reference.y) != (key.kind, key.s, key.y):
            fail("selected scalar-cache reference disagrees with its exact key")
        return reference.qualified_value, reference
    return f"outerEnclosure dyadicBits ({scalar_exact(key)})", None


def render_arguments(name: str, uses: tuple[query_plan.ScalarUse, ...]) -> list[str]:
    lines = [
        f"def {name} : LRUpperKCachedScalarArguments.Arguments :=",
        "  {",
    ]
    for use in uses:
        lines.append(
            f"    {use.field}S := {fraction_text(use.key.s)}, "
            f"{use.field}Y := {fraction_text(use.key.y)}"
        )
    lines[-1] += " }"
    return lines


def render_values(
    name: str,
    uses: tuple[query_plan.ScalarUse, ...],
    args: argparse.Namespace,
    cache: AuthenticatedCache,
) -> tuple[list[str], dict[str, CacheReference | None]]:
    lines = [
        f"def {name} : LRUpperKCachedCornerValues.ScalarValues :=",
        "  {",
    ]
    references: dict[str, CacheReference | None] = {}
    for use in uses:
        expression, reference = scalar_value_expression(use.key, args, cache)
        references[use.field] = reference
        lines.append(f"    {use.field} := {expression}")
    lines[-1] += " }"
    return lines, references


def render_scalar_covers(
    theorem_name: str,
    arguments_name: str,
    values_name: str,
    uses: tuple[query_plan.ScalarUse, ...],
    references: dict[str, CacheReference | None],
) -> list[str]:
    lines = [
        f"theorem {theorem_name} :",
        "    LRUpperKCachedScalarArguments.Covers terms sqrtFuel logFuel",
        f"      {arguments_name} {values_name} := by",
        "  refine",
        "    { aY0Lower := ?_",
        "      aY0Upper := ?_",
        "      cY0Lower := ?_",
        "      cY0Upper := ?_",
        "      aELower := ?_",
        "      aEUpper := ?_",
        "      cELower := ?_",
        "      cEUpper := ?_ }",
    ]
    cache_constants = (
        f"CourtadeKumar.{cache_proofs.GENERATED_NAMESPACE}.terms, "
        f"CourtadeKumar.{cache_proofs.GENERATED_NAMESPACE}.sqrtFuel, "
        f"CourtadeKumar.{cache_proofs.GENERATED_NAMESPACE}.logFuel"
    )
    for use in uses:
        reference = references[use.field]
        if reference is None:
            lines.extend(
                [
                    f"  · simpa [{arguments_name}, {values_name}] using",
                    f"      (outerEnclosure_covers dyadicBits ({scalar_exact(use.key)}))",
                ]
            )
        else:
            lines.extend(
                [
                    f"  · simpa [{arguments_name}, {values_name}, terms, sqrtFuel,",
                    f"      logFuel, {cache_constants}] using",
                    f"      {reference.qualified_covers}",
                ]
            )
    return lines


def render_config(
    prefix: str,
    args: argparse.Namespace,
    authenticated: replay.AuthenticatedInputs,
    cache: AuthenticatedCache,
    adapters: dict[str, object],
) -> tuple[str, str]:
    module = f"{prefix}Config"
    receipt = authenticated.bridge_receipt
    source = f"""import {cache.coverage_module}
import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedScalarArguments
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDirectCachedLeafCertificate

/-! Authenticated constants for the scalar-cached patched upper-`K` replay. -/

namespace CourtadeKumar.{GENERATED_NAMESPACE}

def dyadicBits : ℕ := {args.dyadic_bits}
def terms : ℕ := {args.terms}
def sqrtFuel : ℕ := {authenticated.evaluator["parameters"]["sqrtFuel"]}
def logFuel : ℕ := {authenticated.evaluator["parameters"]["logFuel"]}
def bridgeReceiptPayloadSha256 : String := {json.dumps(receipt.payload_sha256)}
def patchedManifestPayloadSha256 : String :=
  {json.dumps(authenticated.manifest["resultPayloadSha256"])}
def streamsAggregateSha256 : String :=
  {json.dumps(authenticated.manifest["streamsAggregateSha256"])}
def scalarCacheProofPlanSha256 : String :=
  {json.dumps(cache.manifest["planSha256"])}
def scalarCacheResultSetSha256 : String :=
  {json.dumps(cache.manifest["collectionReceipt"]["resultSetSha256"])}
def cachedReplayAdapterSourceSetSha256 : String :=
  {json.dumps(adapters["sourceSetSha256"])}

end CourtadeKumar.{GENERATED_NAMESPACE}
"""
    return module, source


def render_leaf_group(
    prefix: str,
    config_module: str,
    root: replay.AuthenticatedRoot,
    group_index: int,
    entries: list[tuple[int, replay.PlannedNode]],
    args: argparse.Namespace,
    cache: AuthenticatedCache,
) -> tuple[
    str,
    str,
    dict[replay.PathSteps, tuple[str, str, str]],
    int,
    int,
]:
    stem = root.spec.stem
    module = f"{prefix}{stem}LeavesG{group_index:04d}"
    namespace = f"{stem}LeavesG{group_index:04d}"
    lines = [
        f"import {config_module}",
        "",
        "/-! Scalar-cached semantic leaves for authenticated upper-`K` paths. -/",
        "",
        f"namespace CourtadeKumar.{GENERATED_NAMESPACE}",
        f"namespace {namespace}",
        "",
        replay.OPEN_BLOCK.rstrip(),
        "open LRUpperKDyadicOuterRounding",
        "",
    ]
    references: dict[replay.PathSteps, tuple[str, str, str]] = {}
    selected_occurrences = 0
    fallback_occurrences = 0
    for index, planned in entries:
        if not planned.node.is_leaf or planned.node.token != "M":
            fail(f"{module} received a non-leaf arithmetic entry")
        exact_box = query_plan.exact_box_at(root.spec, planned.path)
        center_box = exact_box.center()
        center_uses = query_plan.scalar_uses(center_box)
        whole_uses = query_plan.scalar_uses(exact_box)
        base = f"l{index:05d}"
        path_name = f"{base}p"
        box_name = f"{base}b"
        box_exact_name = f"{base}be"
        center_box_name = f"{base}c"
        center_arguments = f"{base}ca"
        whole_arguments = f"{base}wa"
        center_values = f"{base}csv"
        whole_values = f"{base}wsv"
        center_args_exact = f"{base}cae"
        whole_args_exact = f"{base}wae"
        center_scalar_covers = f"{base}csc"
        whole_scalar_covers = f"{base}wsc"
        center_assembled = f"{base}cv"
        whole_assembled = f"{base}wv"
        center_covers = f"{base}cc"
        whole_covers = f"{base}wc"
        analytic = f"{base}a"
        nodes = f"{base}n"
        evaluation = f"{base}e"
        chunk = base

        center_value_lines, center_refs = render_values(
            center_values, center_uses, args, cache
        )
        whole_value_lines, whole_refs = render_values(
            whole_values, whole_uses, args, cache
        )
        for value in (*center_refs.values(), *whole_refs.values()):
            if value is None:
                fallback_occurrences += 1
            else:
                selected_occurrences += 1

        lines.extend(
            [
                f"def {path_name} : LRUpperKHistoricalPackedCertificate.Path :=",
                f"  {replay.lean_path(planned.path)}",
                "",
                f"def {box_name} : CertificateBox :=",
                f"  {box_lean(exact_box)}",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {box_exact_name} : {box_name} =",
                "    LRUpperKHistoricalPackedCertificate.follow",
                f"      {root.spec.root_lean} {path_name} := by",
                "  rfl'",
                "",
                f"def {center_box_name} : CertificateBox :=",
                f"  LRUpperKHistoricalThreeCoordinateBase.centerBox {box_name}",
                "",
                *render_arguments(center_arguments, center_uses),
                "",
                *render_arguments(whole_arguments, whole_uses),
                "",
                *center_value_lines,
                "",
                *whole_value_lines,
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {center_args_exact} : {center_arguments} =",
                f"    LRUpperKCachedScalarArguments.exact {center_box_name} := by",
                "  rfl'",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {whole_args_exact} : {whole_arguments} =",
                f"    LRUpperKCachedScalarArguments.exact {box_name} := by",
                "  rfl'",
                "",
                *render_scalar_covers(
                    center_scalar_covers,
                    center_arguments,
                    center_values,
                    center_uses,
                    center_refs,
                ),
                "",
                *render_scalar_covers(
                    whole_scalar_covers,
                    whole_arguments,
                    whole_values,
                    whole_uses,
                    whole_refs,
                ),
                "",
                f"def {center_assembled} : LRUpperKCachedCornerValues.Values :=",
                f"  {center_values}.assemble",
                "",
                f"def {whole_assembled} : LRUpperKCachedCornerValues.Values :=",
                f"  {whole_values}.assemble",
                "",
                f"theorem {center_covers} : LRUpperKCachedCornerValues.CoversExact",
                f"    terms {center_box_name}",
                f"      (LRUpperKDirectLeafCertificate.centerCorners",
                f"        sqrtFuel logFuel {box_name}) {center_assembled} := by",
                f"  simpa [{center_assembled}, {center_box_name},",
                "      LRUpperKDirectLeafCertificate.centerCorners] using",
                "    (LRUpperKCachedScalarArguments.coversExact_auto",
                f"      terms sqrtFuel logFuel {center_box_name} {center_arguments}",
                f"      {center_values} {center_args_exact} {center_scalar_covers})",
                "",
                f"theorem {whole_covers} : LRUpperKCachedCornerValues.CoversExact",
                f"    terms {box_name}",
                f"      (LRUpperKDirectLeafCertificate.wholeCorners",
                f"        sqrtFuel logFuel {box_name}) {whole_assembled} := by",
                f"  simpa [{whole_assembled},",
                "      LRUpperKDirectLeafCertificate.wholeCorners] using",
                "    (LRUpperKCachedScalarArguments.coversExact_auto",
                f"      terms sqrtFuel logFuel {box_name} {whole_arguments}",
                f"      {whole_values} {whole_args_exact} {whole_scalar_covers})",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {analytic} : LRUpperKDirectLeafCertificate.analyticCheck",
                f"    terms sqrtFuel logFuel {box_name} = true := by",
                "  rfl'",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {nodes} : LRUpperKDirectCachedLeafCertificate.nodeCheck",
                f"    dyadicBits terms sqrtFuel logFuel {box_name}",
                f"      {center_assembled} {whole_assembled} = true := by",
                "  rfl'",
                "",
                f"set_option maxRecDepth {args.max_rec_depth} in",
                f"set_option maxHeartbeats {args.max_heartbeats} in",
                f"theorem {evaluation} :",
                "    LRUpperKDirectCachedLeafCertificate.evaluationCheck",
                f"      dyadicBits terms sqrtFuel logFuel {box_name}",
                f"        {center_assembled} {whole_assembled} = true := by",
                "  rfl'",
                "",
                f"def {chunk} : LRUpperKDirectCheckedTree.CheckedAtPath",
                f"    {root.spec.root_lean} {path_name} := by",
                f"  rw [← {box_exact_name}]",
                "  exact LRUpperKDirectCachedLeafCertificate.checkedTreeOfFactoredChecks",
                "    dyadicBits terms sqrtFuel logFuel",
                f"    {analytic} {center_covers} {whole_covers} {nodes} {evaluation}",
                "",
            ]
        )
        references[planned.path] = (namespace, path_name, chunk)
    lines.extend(
        [
            f"end {namespace}",
            f"end CourtadeKumar.{GENERATED_NAMESPACE}",
            "",
        ]
    )
    source = "\n".join(lines)
    if source.count("  rfl'\n") != 6 * len(entries):
        fail(f"{module} did not emit exactly six kernel reductions per leaf")
    return (
        module,
        source,
        references,
        selected_occurrences,
        fallback_occurrences,
    )


def render_final_assembly(
    prefix: str, one_module: str, two_module: str
) -> tuple[str, str]:
    module = f"{prefix}Assembly"
    source = f"""import {one_module}
import {two_module}

/-! Final join of the separately rooted scalar-cached patched trees. -/

namespace CourtadeKumar

theorem {FINAL_THEOREM} :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion :=
  LRUpperKDirectCheckedTree.upperKRegionCertificate_of_twoCheckedTrees
    {GENERATED_NAMESPACE}.OneToTwoAssembly.checkedTree
    {GENERATED_NAMESPACE}.TwoToFourAssembly.checkedTree

end CourtadeKumar
"""
    return module, source


def validate_sources(
    sources: dict[str, str], prefix: str, total_leaves: int
) -> None:
    if len(sources) > replay.MAX_GENERATED_MODULES:
        fail("cached replay module count exceeds the global guard")
    if sum(len(source.encode("utf-8")) for source in sources.values()) > (
        replay.MAX_GENERATED_SOURCE_BYTES
    ):
        fail("cached replay source bytes exceed the global guard")
    combined = "\n".join(sources.values())
    for forbidden in replay.FORBIDDEN_LEAN:
        if forbidden in combined:
            fail(f"cached replay contains forbidden Lean token {forbidden!r}")
    if combined.count("  rfl'\n") != 6 * total_leaves:
        fail("cached replay reduction count drifted")
    expected_uses = {
        "LRUpperKDirectLeafCertificate.analyticCheck": total_leaves,
        "LRUpperKDirectCachedLeafCertificate.nodeCheck": total_leaves,
        "LRUpperKDirectCachedLeafCertificate.evaluationCheck": total_leaves,
        "LRUpperKDirectCachedLeafCertificate.checkedTreeOfFactoredChecks": total_leaves,
    }
    for needle, expected in expected_uses.items():
        if combined.count(needle) != expected:
            fail(f"cached replay use count drifted for {needle}")
    if combined.count(f"theorem {FINAL_THEOREM}") != 1:
        fail("cached replay does not export exactly one final theorem")
    replay.validate_generated_graph(sources, prefix)


def build(
    args: argparse.Namespace,
    authenticated: replay.AuthenticatedInputs,
    cache: AuthenticatedCache,
) -> tuple[dict[str, str], dict[str, object]]:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("cached replay generator changed before planning")
    prefix = cached_replay_prefix(args.module_prefix)
    adapters = bind_cached_replay_adapter_sources()
    config_module, config_source = render_config(
        prefix, args, authenticated, cache, adapters
    )
    sources: dict[str, str] = {config_module: config_source}
    root_manifests: list[dict[str, object]] = []
    root_final_modules: dict[str, str] = {}
    total_leaves = 0
    total_structural_nodes = 0
    total_selected_occurrences = 0
    total_fallback_occurrences = 0

    for spec in replay.ROOT_SPECS:
        root = authenticated.roots[spec.key]
        plan = replay.make_plan(root.tree, args.max_chunk_leaves)
        if replay.reconstruct(plan) != root.topology:
            fail(f"{spec.key} cached frontier does not reconstruct its stream")
        frontier_nodes = list(replay.frontier(plan))
        total_leaves += len(frontier_nodes)
        leaf_modules: list[str] = []
        chunk_references: dict[replay.PathSteps, replay.ChunkReference] = {}
        chunk_records: list[dict[str, object]] = []
        groups = replay.chunks_in_groups(frontier_nodes, args.chunks_per_module)
        for group_index, group in enumerate(groups):
            (
                module,
                source,
                references,
                selected_count,
                fallback_count,
            ) = render_leaf_group(
                prefix, config_module, root, group_index, group, args, cache
            )
            if module in sources:
                fail(f"generated cached replay module collision: {module}")
            sources[module] = source
            leaf_modules.append(module)
            total_selected_occurrences += selected_count
            total_fallback_occurrences += fallback_count
            for path, reference in references.items():
                if path in chunk_references:
                    fail(f"duplicate cached leaf path in {spec.key}")
                chunk_references[path] = reference
            for index, planned in group:
                exact_box = query_plan.exact_box_at(spec, planned.path)
                all_uses = (
                    *query_plan.scalar_uses(exact_box.center()),
                    *query_plan.scalar_uses(exact_box),
                )
                selected = sum(
                    cache_key_id(use.key, args) in cache.entries for use in all_uses
                )
                chunk_records.append(
                    {
                        "index": index,
                        "module": module,
                        "path": replay.path_text(planned.path),
                        "bounds": replay.bounds_at(spec, planned.path),
                        "selectedScalarOccurrences": selected,
                        "fallbackScalarOccurrences": 16 - selected,
                    }
                )
        if len(chunk_references) != len(frontier_nodes):
            fail(f"{spec.key} lost a cached leaf reference")

        coverage, leaf_indexes = replay.add_import_fan_in(
            sources,
            prefix,
            f"{spec.stem}LeafCoverage",
            leaf_modules,
            args.max_imports_per_index,
        )
        layer_map = replay.nodes_by_level(plan)
        structural_expected = replay.structural_node_count(plan)
        total_structural_nodes += structural_expected
        internal_references: dict[replay.PathSteps, replay.InternalReference] = {}
        layer_records: list[dict[str, object]] = []
        all_index_modules = list(leaf_indexes)

        for level in sorted(layer_map):
            layer_entries = layer_map[level]
            shards = [
                layer_entries[index : index + args.structural_defs_per_module]
                for index in range(0, len(layer_entries), args.structural_defs_per_module)
            ]
            metadata: list[tuple[str, str, list[replay.PlannedNode]]] = []
            node_records: list[dict[str, object]] = []
            for shard_index, shard in enumerate(shards):
                module = f"{prefix}{spec.stem}Layer{level:02d}S{shard_index:04d}"
                namespace = f"{spec.stem}Layer{level:02d}S{shard_index:04d}"
                for planned in shard:
                    if planned.path in internal_references:
                        fail(f"duplicate cached structural path in {spec.key}")
                    internal_references[planned.path] = (
                        namespace,
                        f"node_{replay.path_identifier(planned.path)}",
                    )
                    node_records.append(
                        {
                            "path": replay.path_text(planned.path),
                            "axis": planned.node.token,
                            "module": module,
                        }
                    )
                metadata.append((module, namespace, shard))
            shard_modules: list[str] = []
            for module, namespace, shard in metadata:
                source = replay.render_structural_shard(
                    coverage,
                    root,
                    module,
                    namespace,
                    shard,
                    chunk_references,
                    internal_references,
                )
                if module in sources:
                    fail(f"cached structural module collision: {module}")
                sources[module] = source
                shard_modules.append(module)
            previous_coverage = coverage
            coverage, indexes = replay.add_import_fan_in(
                sources,
                prefix,
                f"{spec.stem}Layer{level:02d}Coverage",
                [previous_coverage, *shard_modules],
                args.max_imports_per_index,
            )
            all_index_modules.extend(indexes)
            layer_records.append(
                {
                    "level": level,
                    "nodeCount": len(layer_entries),
                    "inputCoverageModule": previous_coverage,
                    "shardModules": shard_modules,
                    "outputCoverageModule": coverage,
                    "nodes": node_records,
                }
            )
        if len(internal_references) != structural_expected:
            fail(f"{spec.key} lost a cached structural reference")
        root_module, root_source = replay.render_root_final(
            coverage,
            root,
            prefix,
            plan,
            chunk_references,
            internal_references,
        )
        if root_module in sources:
            fail(f"cached root module collision: {root_module}")
        sources[root_module] = root_source
        root_final_modules[spec.key] = root_module
        root_manifests.append(
            {
                "key": spec.key,
                "rootLean": spec.root_lean,
                "input": replay.relative_project_path(root.path),
                "inputByteSha256": sha256_bytes(root.file_bytes),
                "inputTopologySha256": replay.sha256_text(root.topology),
                "nodes": root.stats.nodes,
                "leaves": root.stats.leaves,
                "maxDepth": root.stats.max_depth,
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
        fail("cached final assembly module collision")
    sources[final_module] = final_source
    validate_sources(sources, prefix, total_leaves)
    if total_selected_occurrences + total_fallback_occurrences != 16 * total_leaves:
        fail("cached scalar occurrence accounting drifted")
    if total_selected_occurrences != cache.query_manifest[
        "selectedScalarOccurrences"
    ]:
        fail("cached replay selected occurrences disagree with the query plan")

    output_hashes = {
        f"{module}.lean": sha256_bytes(source.encode("utf-8"))
        for module, source in sorted(sources.items())
    }
    manifest_core: dict[str, object] = {
        "format": FORMAT,
        "generator": {"file": SCRIPT.name, "byteSha256": SCRIPT_BYTE_SHA256},
        "proofAuthority": PROOF_AUTHORITY,
        "authenticatedInputs": {
            "bridgeReceiptPayloadSha256": authenticated.bridge_receipt.payload_sha256,
            "patchedManifestPayloadSha256": authenticated.manifest[
                "resultPayloadSha256"
            ],
            "streamsAggregateSha256": authenticated.manifest[
                "streamsAggregateSha256"
            ],
        },
        "scalarCacheProof": {
            "file": replay.relative_project_path(cache.path),
            "byteSha256": sha256_bytes(cache.file_bytes),
            "planSha256": cache.manifest["planSha256"],
            "entryCount": len(cache.entries),
            "coverageModule": cache.coverage_module,
        },
        "cachedReplayAdapterImplementation": adapters,
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
        "outputDirectory": replay.relative_project_path(args.validated_output_dir),
        "totalLeaves": total_leaves,
        "totalKernelReductions": 6 * total_leaves,
        "selectedScalarOccurrences": total_selected_occurrences,
        "fallbackScalarOccurrences": total_fallback_occurrences,
        "totalStructuralNodes": total_structural_nodes,
        "leanModuleCount": len(sources),
        "roots": root_manifests,
        "outputs": output_hashes,
        "finalModule": final_module,
        "finalTheorem": f"CourtadeKumar.{FINAL_THEOREM}",
    }
    plan_sha = sha256_bytes(canonical_json_bytes(manifest_core))
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("cached replay generator changed while rendering")
    if bind_cached_replay_adapter_sources() != adapters:
        fail("cached replay adapter changed while rendering")
    if authenticate_cache(args, authenticated) != cache:
        fail("scalar-cache proof inputs changed while cached replay rendered")
    return sources, {**manifest_core, "planSha256": plan_sha}


def summary(manifest: dict[str, object]) -> dict[str, object]:
    return {
        "status": "validated-read-only",
        "planSha256": manifest["planSha256"],
        "scalarCacheProofPlanSha256": manifest["scalarCacheProof"]["planSha256"],
        "outputDirectory": manifest["outputDirectory"],
        "totalLeaves": manifest["totalLeaves"],
        "totalKernelReductions": manifest["totalKernelReductions"],
        "selectedScalarOccurrences": manifest["selectedScalarOccurrences"],
        "fallbackScalarOccurrences": manifest["fallbackScalarOccurrences"],
        "totalStructuralNodes": manifest["totalStructuralNodes"],
        "leanModuleCount": manifest["leanModuleCount"],
        "finalModule": manifest["finalModule"],
        "finalTheorem": manifest["finalTheorem"],
    }


def validate_arguments(args: argparse.Namespace) -> None:
    replay.validate_positive_arguments(args)
    cached_replay_prefix(args.module_prefix)


def prepared(
    args: argparse.Namespace,
) -> tuple[dict[str, str], dict[str, object]]:
    replay.validate_repository_location()
    validate_arguments(args)
    (
        args.validated_output_dir,
        args.validated_output_identity,
    ) = replay.output_directory(args.output_dir)
    authenticated = replay.authenticate_inputs(args)
    args.authenticated_sqrt_fuel = authenticated.evaluator["parameters"]["sqrtFuel"]
    args.authenticated_log_fuel = authenticated.evaluator["parameters"]["logFuel"]
    cache = authenticate_cache(args, authenticated)
    return build(args, authenticated, cache)


def command_plan(args: argparse.Namespace) -> None:
    _sources, manifest = prepared(args)
    print(json.dumps(summary(manifest), indent=2, sort_keys=True))


def command_generate(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        fail("refusing cached replay emission without --confirm-write")
    sources, manifest = prepared(args)
    expected = replay.supplied_hex64(
        args.expected_plan_sha256, "--expected-plan-sha256"
    )
    if expected != manifest["planSha256"]:
        fail("--expected-plan-sha256 differs from the fresh cached replay plan")
    directory: Path = args.validated_output_dir
    manifest_name = f"{cached_replay_prefix(args.module_prefix)}Manifest.json"
    outputs = {
        replay.safe_output_path(directory, f"{module}.lean"): source.encode("utf-8")
        for module, source in sources.items()
    }
    manifest_path = replay.safe_output_path(directory, manifest_name)
    outputs[manifest_path] = pretty_json_bytes(manifest)
    collisions = [path.name for path in outputs if path.exists() or path.is_symlink()]
    if collisions:
        fail(f"refusing to overwrite cached replay outputs: {sorted(collisions)}")
    replay.exclusive_create_all(directory, args.validated_output_identity, outputs)
    written = summary(manifest)
    written.update(
        {"status": "written", "writtenFiles": len(outputs), "manifest": manifest_name}
    )
    print(json.dumps(written, sort_keys=True))


def add_arguments(command: argparse.ArgumentParser) -> None:
    replay.add_common_arguments(command)
    command.add_argument("--cache-proof-manifest", required=True)
    command.add_argument("--cache-proof-manifest-sha256", required=True)
    command.add_argument("--cache-proof-plan-sha256", required=True)
    command.set_defaults(
        module_prefix="AgentUpperKHistoricalPatchedCachedReplayGenerated"
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="authenticate and plan without writing")
    add_arguments(plan)
    plan.set_defaults(handler=command_plan)
    generate = commands.add_parser(
        "generate", help="emit the scalar-cached semantic replay"
    )
    add_arguments(generate)
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
    except replay.ReplayPlanError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
