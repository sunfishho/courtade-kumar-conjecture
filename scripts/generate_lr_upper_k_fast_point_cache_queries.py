#!/usr/bin/env python3
"""Plan or emit fast shared-point queries for the patched upper-``K`` replay.

The historical replay reconstructs eight ``A/C`` scalar calls for both the
center and the whole box of every authenticated leaf.  Those calls share many
of the same positive rational arguments of ``Q`` and ``Q'``.  This tool:

* authenticates the same bridge receipt, patched streams, topology, evaluator,
  and Lean implementation as the direct replay;
* reconstructs every box with the independently checked exact geometry from
  ``generate_lr_upper_k_scalar_cache_queries``;
* deduplicates point arguments inside each leaf before applying a global
  leaf-multiplicity threshold; and
* emits bounded Lean modules that use the small-range polynomial square-root
  certificate and print its four logarithm range reductions together with
  rounded ``Q`` and ``Q'`` enclosures.

The query output is untrusted.  A later ingestion stage must serialize the
range reductions and rounded endpoints and authenticate them with ordinary
kernel-checked arithmetic and reduction.  Each module contains one compiled
``#eval`` action which streams one row per point, avoiding both repeated
evaluator startup and retention of a large result list.  Emission uses
exclusive creation inside a pinned, existing repository-local scratch child.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable, Iterator

import generate_lr_upper_k_historical_patched_replay as replay
import generate_lr_upper_k_scalar_cache_queries as scalar_geometry


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
FORMAT = "authenticated patched upper-K fast point-cache query plan v3"
CACHE_KEY_SCHEMA = "upper-k-fast-point-cache-key-v2"
QUERY_ROW_SCHEMA = "upper-k-fast-point-cache-query-row-v3"
FAST_CERTIFICATE_SCHEME = (
    "lr-q-small-range-binomial-six-plus-y7-lower-rounded-sqrt-log-v1"
)
PROOF_AUTHORITY = (
    "none: query output is untrusted data; later ordinary Lean kernel-checked "
    "arithmetic and reduction are the sole proof authority"
)
FAST_POINT_SOURCE_FILES = (
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantFastQPointCertificate.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKCachedLogPointCore.lean",
)
MAX_SELECTED_POINTS = 100_000
MAX_QUERY_MODULES = 20_000
MAX_MANIFEST_BYTES = 64 * 1024 * 1024


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def pretty_json_bytes(value: object) -> bytes:
    data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if len(data) > MAX_MANIFEST_BYTES:
        replay.fail("fast point-cache manifest exceeds its hard byte guard")
    return data


def fraction_record(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def chunks(values: list[Any], size: int) -> Iterator[list[Any]]:
    for index in range(0, len(values), size):
        yield values[index : index + size]


def query_module_prefix(raw: str) -> str:
    if re.fullmatch(r"Agent[A-Za-z0-9]+", raw) is None or len(raw) > 80:
        replay.fail("--module-prefix must be an ASCII Agent-prefixed Lean identifier")
    return raw


def bind_fast_point_sources() -> dict[str, object]:
    records: list[dict[str, object]] = []
    for relative in FAST_POINT_SOURCE_FILES:
        path = replay.project_path(relative, f"fast point source {relative}")
        data = replay.read_regular_file(
            path, f"fast point source {relative}", replay.MAX_INPUT_BYTES
        )
        records.append(
            {"file": relative, "bytes": len(data), "byteSha256": sha256_bytes(data)}
        )
    core: dict[str, object] = {
        "algorithm": replay.DIRECT_REPLAY_SOURCE_SET_ALGORITHM,
        "files": records,
    }
    return {**core, "sourceSetSha256": sha256_bytes(canonical_json_bytes(core))}


def cache_key_payload(point: Fraction, args: argparse.Namespace) -> dict[str, object]:
    return {
        "schema": CACHE_KEY_SCHEMA,
        "certificateScheme": FAST_CERTIFICATE_SCHEME,
        "z": fraction_record(point),
        "pointDyadicBits": args.dyadic_bits,
        "logDyadicBits": args.dyadic_bits,
        "sqrtDyadicBits": args.point_sqrt_bits,
        "terms": args.terms,
        "logFuel": args.authenticated_log_fuel,
    }


def cache_id(point: Fraction, args: argparse.Namespace) -> str:
    return sha256_bytes(canonical_json_bytes(cache_key_payload(point, args)))


def point_uses(box: scalar_geometry.ExactBox) -> set[Fraction]:
    """Positive point arguments after respecting exact zero scalar branches."""
    result: set[Fraction] = set()
    for use in scalar_geometry.scalar_uses(box):
        s, y = use.key.s, use.key.y
        # Both aEnclosure and cEnclosure return the exact zero point when y=0.
        if y == 0:
            continue
        b = s + (1 - s) * y
        if use.key.kind == "a":
            result.update((s, b))
        else:
            result.update((s, y, b))
    return result


def raw_point_occurrences(box: scalar_geometry.ExactBox) -> int:
    """Point occurrences before any sharing, excluding exact zero branches."""
    result = 0
    for use in scalar_geometry.scalar_uses(box):
        if use.key.y == 0:
            continue
        result += 2 if use.key.kind == "a" else 3
    return result


def render_query_module(
    prefix: str,
    index: int,
    entries: list[tuple[str, Fraction, int]],
    args: argparse.Namespace,
) -> tuple[str, str]:
    module = f"{prefix}Q{index:04d}"
    namespace = f"CourtadeKumar.{module}"
    request_rows = ",\n    ".join(
        f"({json.dumps(identifier)}, ({fraction_text(point)}))"
        for identifier, point, _multiplicity in entries
    )
    lines = [
        "import InformationTheory.CourtadeKumar.LRDeterminantFastQPointCertificate",
        "import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedLogPointCore",
        "",
        "/-! Untrusted fast point-cache queries; no theorem imports this output. -/",
        "",
        f"namespace {namespace}",
        "",
        "abbrev QueryRequest := String × ℚ",
        "",
        "def requests : List QueryRequest :=",
        f"  [{request_rows}]",
        "",
        "def row (request : QueryRequest) : String :=",
        "  let identifier := request.1",
        "  let z := request.2",
        "  let certificate :=",
        "    LRQFastPointCertificate.roundedAuto",
        f"      {args.point_sqrt_bits} {args.authenticated_log_fuel} z",
        "  let logLower := LRUpperKDyadicOuterRounding.outerEnclosure",
        f"    {args.dyadic_bits} (certificate.logLowerProbability.enclosure {args.terms})",
        "  let logUpper := LRUpperKDyadicOuterRounding.outerEnclosure",
        f"    {args.dyadic_bits} (certificate.logUpperProbability.enclosure {args.terms})",
        "  let logs : LRUpperKCachedLogPointCore.LogValues :=",
        "    { lower := logLower, upper := logUpper }",
        "  let values := LRUpperKCachedLogPointCore.outerValues",
        f"    {args.dyadic_bits}",
        "      (LRUpperKCachedLogPointCore.rawValues certificate logs)",
        "  String.intercalate \"\\t\"",
        "    [identifier, reprStr z,",
        "      reprStr certificate.sqrtOneSub.lower,",
        "      reprStr certificate.sqrtOneSub.upper,",
        "      reprStr certificate.logLowerProbability.lower.exponent,",
        "      reprStr certificate.logLowerProbability.lower.mantissa,",
        "      reprStr certificate.logLowerProbability.upper.exponent,",
        "      reprStr certificate.logLowerProbability.upper.mantissa,",
        "      reprStr certificate.logUpperProbability.lower.exponent,",
        "      reprStr certificate.logUpperProbability.lower.mantissa,",
        "      reprStr certificate.logUpperProbability.upper.exponent,",
        "      reprStr certificate.logUpperProbability.upper.mantissa,",
        "      reprStr logLower.lower, reprStr logLower.upper,",
        "      reprStr logUpper.lower, reprStr logUpper.upper,",
        "      reprStr values.q.lower, reprStr values.q.upper,",
        "      reprStr values.qPrime.lower, reprStr values.qPrime.upper]",
        "",
        "set_option maxRecDepth 1000000 in",
        "#eval requests.forM fun request => IO.println (row request)",
        "",
        f"end {namespace}",
        "",
    ]
    source = "\n".join(lines)
    if source.count("#eval ") != 1:
        replay.fail(f"{module} must contain exactly one streaming #eval")
    if source.count(json.dumps(entries[0][0])) != 1:
        replay.fail(f"{module} first cache ID drifted during rendering")
    for identifier, _point, _multiplicity in entries:
        if source.count(json.dumps(identifier)) != 1:
            replay.fail(f"{module} cache ID multiplicity drifted during rendering")
    for forbidden in replay.FORBIDDEN_LEAN:
        if forbidden in source:
            replay.fail(f"{module} contains forbidden Lean token {forbidden!r}")
    return module, source


def authenticated_point_counts(
    authenticated: replay.AuthenticatedInputs,
) -> tuple[
    Counter[Fraction], Counter[str], Counter[int], int, int, int
]:
    counts: Counter[Fraction] = Counter()
    root_leaves: Counter[str] = Counter()
    leaf_widths: Counter[int] = Counter()
    leaf_count = 0
    raw_occurrences = 0
    local_distinct = 0
    for root_key, _path, box in scalar_geometry.authenticated_leaves(authenticated):
        leaf_count += 1
        root_leaves[root_key] += 1
        center_points = point_uses(box.center())
        whole_points = point_uses(box)
        points = center_points | whole_points
        raw_occurrences += raw_point_occurrences(box.center()) + raw_point_occurrences(
            box
        )
        local_distinct += len(points)
        leaf_widths[len(points)] += 1
        # Sorting within a leaf makes first-use order deterministic while the
        # authenticated frontier traversal preserves downstream import locality.
        counts.update(sorted(points))

    expected_leaves = sum(root.stats.leaves for root in authenticated.roots.values())
    if leaf_count != expected_leaves or sum(root_leaves.values()) != leaf_count:
        replay.fail("fast point-cache leaf count disagrees with authenticated streams")
    if sum(counts.values()) != local_distinct:
        replay.fail("fast point-cache leaf-local multiplicity accounting drifted")
    if raw_occurrences < local_distinct:
        replay.fail("fast point-cache raw occurrence count is below local sharing")
    if not counts or min(counts) <= 0 or max(counts) > Fraction(1, 16):
        replay.fail("fast point-cache domain escaped (0,1/16]")
    return (
        counts,
        root_leaves,
        leaf_widths,
        leaf_count,
        raw_occurrences,
        local_distinct,
    )


def build(
    args: argparse.Namespace, authenticated: replay.AuthenticatedInputs
) -> tuple[dict[str, str], dict[str, object]]:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        replay.fail("fast point-cache generator changed during planning")
    if sha256_bytes(replay.SCRIPT.read_bytes()) != replay.SCRIPT_BYTE_SHA256:
        replay.fail("direct replay generator changed during fast point planning")
    if (
        sha256_bytes(scalar_geometry.SCRIPT.read_bytes())
        != scalar_geometry.SCRIPT_BYTE_SHA256
    ):
        replay.fail("scalar geometry generator changed during fast point planning")

    args.authenticated_log_fuel = authenticated.evaluator["parameters"]["logFuel"]
    direct_sources = replay.bind_direct_replay_sources()
    fast_sources = bind_fast_point_sources()
    (
        counts,
        root_leaves,
        leaf_widths,
        leaf_count,
        raw_occurrences,
        local_distinct,
    ) = authenticated_point_counts(authenticated)

    first_use_ordinals = {point: ordinal for ordinal, point in enumerate(counts)}
    selected = [
        (cache_id(point, args), point, multiplicity)
        for point, multiplicity in counts.items()
        if multiplicity >= args.cache_multiplicity_threshold
    ]
    if len(selected) > MAX_SELECTED_POINTS:
        replay.fail("selected fast point-cache keys exceed the hard guard")
    if len({identifier for identifier, _point, _count in selected}) != len(selected):
        replay.fail("content-address collision among selected fast point-cache keys")
    query_groups = list(chunks(selected, args.queries_per_module))
    if len(query_groups) > MAX_QUERY_MODULES:
        replay.fail("fast point-cache query modules exceed the hard guard")

    prefix = query_module_prefix(args.module_prefix)
    sources: dict[str, str] = {}
    query_records: list[dict[str, object]] = []
    selected_records: list[dict[str, object]] = []
    for index, group in enumerate(query_groups):
        module, source = render_query_module(prefix, index, group, args)
        if module in sources:
            replay.fail(f"duplicate fast point-cache query module {module}")
        sources[module] = source
        query_records.append(
            {
                "module": module,
                "firstCacheId": group[0][0],
                "lastCacheId": group[-1][0],
                "queryCount": len(group),
                "streamingEvalCount": 1,
            }
        )
        for entry_index, (identifier, point, multiplicity) in enumerate(group):
            selected_records.append(
                {
                    "cacheId": identifier,
                    "z": fraction_record(point),
                    "leafMultiplicity": multiplicity,
                    "firstUseOrdinal": first_use_ordinals[point],
                    "queryModule": module,
                    "queryIndex": entry_index,
                }
            )

    output_hashes = {
        f"{module}.lean": sha256_bytes(source.encode("utf-8"))
        for module, source in sorted(sources.items())
    }
    selected_occurrences = sum(
        multiplicity for _identifier, _point, multiplicity in selected
    )
    fallback_occurrences = local_distinct - selected_occurrences
    resulting_materializations = len(selected) + fallback_occurrences
    receipt = authenticated.bridge_receipt
    manifest_core: dict[str, object] = {
        "format": FORMAT,
        "generator": {
            "file": SCRIPT.name,
            "byteSha256": SCRIPT_BYTE_SHA256,
            "directReplayGeneratorFile": replay.SCRIPT.name,
            "directReplayGeneratorByteSha256": replay.SCRIPT_BYTE_SHA256,
            "scalarGeometryGeneratorFile": scalar_geometry.SCRIPT.name,
            "scalarGeometryGeneratorByteSha256": (
                scalar_geometry.SCRIPT_BYTE_SHA256
            ),
        },
        "proofAuthority": PROOF_AUTHORITY,
        "queryOutput": {
            "schema": QUERY_ROW_SCHEMA,
            "transport": (
                "one raw ASCII-TAB-separated line per point from one #eval per module; "
                "all non-ID fields are atomic Lean Repr values"
            ),
            "separator": "ASCII TAB",
            "columnCount": 20,
            "columns": [
                "cacheId",
                "z",
                "sqrt.lower",
                "sqrt.upper",
                "logLower.lower.exponent",
                "logLower.lower.mantissa",
                "logLower.upper.exponent",
                "logLower.upper.mantissa",
                "logUpper.lower.exponent",
                "logUpper.lower.mantissa",
                "logUpper.upper.exponent",
                "logUpper.upper.mantissa",
                "logLowerEnclosure.lower",
                "logLowerEnclosure.upper",
                "logUpperEnclosure.lower",
                "logUpperEnclosure.upper",
                "q.lower",
                "q.upper",
                "qPrime.lower",
                "qPrime.upper",
            ],
        },
        "authenticatedInputs": {
            "bridgeReceipt": {
                "file": replay.relative_project_path(receipt.path),
                "byteSha256": sha256_bytes(receipt.file_bytes),
                "payloadSha256": receipt.payload_sha256,
                "profileSha256": receipt.profile_sha256,
                "aggregatePayloadSha256": receipt.aggregate_payload_sha256,
                "aggregateInputSetSha256": receipt.aggregate_input_set_sha256,
            },
            "patchedManifest": {
                "file": replay.relative_project_path(authenticated.manifest_path),
                "byteSha256": sha256_bytes(authenticated.manifest_bytes),
                "payloadSha256": authenticated.manifest["resultPayloadSha256"],
            },
            "streamsAggregateSha256": authenticated.manifest[
                "streamsAggregateSha256"
            ],
            "evaluator": authenticated.evaluator,
            "roots": {
                key: {
                    "byteSha256": sha256_bytes(root.file_bytes),
                    "topologySha256": replay.sha256_text(root.topology),
                    "leaves": root.stats.leaves,
                }
                for key, root in authenticated.roots.items()
            },
        },
        "implementation": {
            "directReplay": direct_sources,
            "fastPointCache": fast_sources,
        },
        "parameters": {
            "cacheKeySchema": CACHE_KEY_SCHEMA,
            "certificateScheme": FAST_CERTIFICATE_SCHEME,
            "pointDyadicBits": args.dyadic_bits,
            "logDyadicBits": args.dyadic_bits,
            "sqrtDyadicBits": args.point_sqrt_bits,
            "terms": args.terms,
            "logFuel": args.authenticated_log_fuel,
            "cacheMultiplicityThreshold": args.cache_multiplicity_threshold,
            "queriesPerModule": args.queries_per_module,
            "modulePrefix": prefix,
            "queryOrdering": (
                "authenticated root/frontier first use, ascending rational within leaf"
            ),
        },
        "outputDirectory": replay.relative_project_path(args.validated_output_dir),
        "rootLeaves": dict(sorted(root_leaves.items())),
        "totalLeaves": leaf_count,
        "rawPointOccurrences": raw_occurrences,
        "leafLocalDistinctPointOccurrences": local_distinct,
        "leafDistinctWidths": {
            str(width): multiplicity
            for width, multiplicity in sorted(leaf_widths.items())
        },
        "uniquePointKeys": len(counts),
        "minimumPoint": fraction_record(min(counts)),
        "maximumPoint": fraction_record(max(counts)),
        "selectedPointKeys": len(selected),
        "selectedPointLeafOccurrences": selected_occurrences,
        "localFallbackPointOccurrences": fallback_occurrences,
        "resultingPointMaterializations": resulting_materializations,
        "eliminatedLeafDuplicateMaterializations": (
            local_distinct - resulting_materializations
        ),
        "eliminatedRawPointMaterializations": (
            raw_occurrences - resulting_materializations
        ),
        "queryModuleCount": len(sources),
        "queries": query_records,
        "selected": selected_records,
        "outputs": output_hashes,
    }
    plan_sha = sha256_bytes(canonical_json_bytes(manifest_core))

    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        replay.fail("fast point-cache generator changed while rendering")
    if sha256_bytes(replay.SCRIPT.read_bytes()) != replay.SCRIPT_BYTE_SHA256:
        replay.fail("direct replay generator changed while rendering fast points")
    if (
        sha256_bytes(scalar_geometry.SCRIPT.read_bytes())
        != scalar_geometry.SCRIPT_BYTE_SHA256
    ):
        replay.fail("scalar geometry generator changed while rendering fast points")
    if replay.bind_direct_replay_sources() != direct_sources:
        replay.fail("direct replay implementation changed while rendering fast points")
    if bind_fast_point_sources() != fast_sources:
        replay.fail("fast point implementation changed while rendering queries")
    return sources, {**manifest_core, "planSha256": plan_sha}


def summary(manifest: dict[str, object]) -> dict[str, object]:
    return {
        "status": "validated-read-only",
        "planSha256": manifest["planSha256"],
        "bridgeReceiptPayloadSha256": manifest["authenticatedInputs"][
            "bridgeReceipt"
        ]["payloadSha256"],
        "outputDirectory": manifest["outputDirectory"],
        "totalLeaves": manifest["totalLeaves"],
        "rawPointOccurrences": manifest["rawPointOccurrences"],
        "leafLocalDistinctPointOccurrences": manifest[
            "leafLocalDistinctPointOccurrences"
        ],
        "uniquePointKeys": manifest["uniquePointKeys"],
        "selectedPointKeys": manifest["selectedPointKeys"],
        "selectedPointLeafOccurrences": manifest[
            "selectedPointLeafOccurrences"
        ],
        "localFallbackPointOccurrences": manifest[
            "localFallbackPointOccurrences"
        ],
        "resultingPointMaterializations": manifest[
            "resultingPointMaterializations"
        ],
        "queryModuleCount": manifest["queryModuleCount"],
    }


def validate_arguments(args: argparse.Namespace) -> None:
    replay.validate_positive_arguments(args)
    if not 1 <= args.cache_multiplicity_threshold <= 1_000_000:
        replay.fail("--cache-multiplicity-threshold must lie in [1,1000000]")
    if not 1 <= args.queries_per_module <= 64:
        replay.fail("--queries-per-module must lie in [1,64]")
    if not 8 <= args.point_sqrt_bits <= 128:
        replay.fail("--point-sqrt-bits must lie in [8,128]")
    query_module_prefix(args.module_prefix)


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
    return build(args, authenticated)


def command_plan(args: argparse.Namespace) -> None:
    _sources, manifest = prepared(args)
    print(json.dumps(summary(manifest), indent=2, sort_keys=True))


def command_generate_queries(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        replay.fail("refusing fast point query emission without --confirm-write")
    sources, manifest = prepared(args)
    expected = replay.supplied_hex64(
        args.expected_plan_sha256, "--expected-plan-sha256"
    )
    if expected != manifest["planSha256"]:
        replay.fail("--expected-plan-sha256 differs from the fresh fast point plan")
    directory: Path = args.validated_output_dir
    manifest_name = f"{query_module_prefix(args.module_prefix)}Manifest.json"
    outputs = {
        replay.safe_output_path(directory, f"{module}.lean"): source.encode("utf-8")
        for module, source in sources.items()
    }
    manifest_path = replay.safe_output_path(directory, manifest_name)
    outputs[manifest_path] = pretty_json_bytes(manifest)
    collisions = [path.name for path in outputs if path.exists() or path.is_symlink()]
    if collisions:
        replay.fail(
            f"refusing to overwrite fast point-cache outputs: {sorted(collisions)}"
        )
    replay.exclusive_create_all(directory, args.validated_output_identity, outputs)
    written = summary(manifest)
    written.update(
        {"status": "written", "writtenFiles": len(outputs), "manifest": manifest_name}
    )
    print(json.dumps(written, sort_keys=True))


def add_arguments(command: argparse.ArgumentParser) -> None:
    replay.add_common_arguments(command)
    command.add_argument("--cache-multiplicity-threshold", type=int, default=2)
    command.add_argument("--queries-per-module", type=int, default=32)
    command.add_argument("--point-sqrt-bits", type=int, default=40)
    command.set_defaults(
        dyadic_bits=40,
        module_prefix="AgentUpperKFastPointCacheQueryGenerated",
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="authenticate and plan without writing")
    add_arguments(plan)
    plan.set_defaults(handler=command_plan)
    generate = commands.add_parser(
        "generate-queries", help="emit bounded untrusted fast point query modules"
    )
    add_arguments(generate)
    generate.add_argument("--expected-plan-sha256", required=True)
    generate.add_argument("--confirm-write", action="store_true")
    generate.set_defaults(handler=command_generate_queries)
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
