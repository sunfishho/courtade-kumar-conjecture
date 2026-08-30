#!/usr/bin/env python3
"""Plan or emit kernel-authenticated upper-``K`` scalar cache modules.

This stage authenticates the query plan, the complete collection receipt, and
every collected output byte.  It then emits literal rational enclosures with
one ordinary ``rfl'`` equality per selected scalar key.  The equality checks
the literal against the exact deterministic ``outerEnclosure`` computation;
``outerEnclosure_covers`` transports that equality to the semantic cover used
by cached leaves.

The Python parser and collected values remain untrusted.  Only the generated
Lean reductions and the already-proved cover theorem have proof authority.
Emission is exclusive and confined to a dedicated existing ``.lake/scratch``
child directory.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import stat
import sys
from typing import Any, Iterable, Iterator

import collect_lr_upper_k_scalar_cache_queries as collection


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
FORMAT = "kernel-authenticated upper-K scalar-cache proof plan v1"
PROOF_AUTHORITY = (
    "one ordinary Lean rfl' reduction per scalar literal, followed by the "
    "proved outerEnclosure_covers theorem"
)
MAX_RECEIPT_BYTES = 32 * 1024 * 1024
MAX_GENERATED_MODULES = 20_000
MAX_GENERATED_SOURCE_BYTES = 256 * 1024 * 1024
GENERATED_NAMESPACE = "LRUpperKHistoricalScalarCacheProofGenerated"


@dataclass(frozen=True, slots=True)
class CacheEntry:
    cache_id: str
    kind: str
    s: Fraction
    y: Fraction
    multiplicity: int
    value: collection.ParsedValue


def fail(message: str) -> None:
    raise collection.query_plan.replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return collection.canonical_json_bytes(value)


def pretty_json_bytes(value: object) -> bytes:
    return collection.pretty_json_bytes(value)


def read_regular_file(path: Path, context: str, maximum: int) -> bytes:
    return collection.read_regular_file(path, context, maximum)


def scratch_directory(raw: str, option: str) -> tuple[Path, tuple[int, int]]:
    path = collection.query_plan.replay.project_path(raw, option)
    try:
        path.relative_to(SCRATCH)
    except ValueError:
        fail(f"{option} must be inside repository-local .lake/scratch")
    if path == SCRATCH:
        fail(f"{option} must be a dedicated scratch child")
    metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        fail(f"{option} must be a real existing directory")
    return path, (metadata.st_dev, metadata.st_ino)


def fraction_from_record(value: object, context: str) -> Fraction:
    if (
        not isinstance(value, list)
        or len(value) != 2
        or not isinstance(value[0], int)
        or isinstance(value[0], bool)
        or not isinstance(value[1], int)
        or isinstance(value[1], bool)
        or value[1] <= 0
    ):
        fail(f"{context} is not a canonical rational pair")
    result = Fraction(value[0], value[1])
    if [result.numerator, result.denominator] != value:
        fail(f"{context} is not reduced with positive denominator")
    return result


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def proof_module_prefix(raw: str) -> str:
    if re.fullmatch(r"Agent[A-Za-z0-9]+", raw) is None or len(raw) > 80:
        fail("--module-prefix must be an ASCII Agent-prefixed Lean identifier")
    return raw


def chunks(values: list[Any], size: int) -> Iterator[list[Any]]:
    for index in range(0, len(values), size):
        yield values[index : index + size]


def load_query_manifest(
    query_dir: Path, manifest_path: Path
) -> tuple[dict[str, Any], list[tuple[str, Path, list[str]]], bytes]:
    if manifest_path.parent != query_dir:
        fail("--query-manifest must be directly inside --query-dir")
    data = read_regular_file(
        manifest_path, "scalar-cache query manifest", collection.MAX_MANIFEST_BYTES
    )
    manifest = collection.strict_manifest(manifest_path, query_dir)
    modules = collection.expected_modules(manifest, query_dir)
    return manifest, modules, data


def load_collection_receipt(
    receipt_path: Path,
    collection_dir: Path,
    query_manifest_path: Path,
    query_manifest_bytes: bytes,
    query_manifest: dict[str, Any],
    modules: list[tuple[str, Path, list[str]]],
) -> tuple[dict[str, Any], dict[str, collection.ParsedValue], bytes]:
    if receipt_path.parent != collection_dir:
        fail("--collection-receipt must be directly inside --collection-dir")
    data = read_regular_file(
        receipt_path, "scalar-cache collection receipt", MAX_RECEIPT_BYTES
    )
    try:
        receipt = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse scalar-cache collection receipt: {error}")
    if not isinstance(receipt, dict):
        fail("scalar-cache collection receipt must be a JSON object")
    payload_sha = receipt.get("receiptPayloadSha256")
    if not isinstance(payload_sha, str) or re.fullmatch(r"[0-9a-f]{64}", payload_sha) is None:
        fail("collection receipt payload hash is invalid")
    core = dict(receipt)
    del core["receiptPayloadSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != payload_sha:
        fail("collection receipt payload hash does not authenticate its content")
    if receipt.get("format") != collection.RECEIPT_FORMAT:
        fail("collection receipt format drifted")
    expected_collector = {
        "file": collection.SCRIPT.name,
        "byteSha256": collection.SCRIPT_BYTE_SHA256,
    }
    if receipt.get("collector") != expected_collector:
        fail("collection receipt is not bound to the current committed collector")
    checker_bytes = read_regular_file(
        collection.CHECKER, "repository-local Lean checker", 64_000
    )
    if receipt.get("checker") != {
        "file": collection.CHECKER.name,
        "byteSha256": sha256_bytes(checker_bytes),
    }:
        fail("collection receipt checker binding drifted")
    query_record = receipt.get("queryManifest")
    expected_query_record = {
        "file": collection.query_plan.replay.relative_project_path(
            query_manifest_path
        ),
        "byteSha256": sha256_bytes(query_manifest_bytes),
        "planSha256": query_manifest["planSha256"],
    }
    if query_record != expected_query_record:
        fail("collection receipt query-manifest binding drifted")
    if receipt.get("moduleCount") != len(modules) or receipt.get(
        "valueCount"
    ) != query_manifest["selectedScalarKeys"]:
        fail("collection receipt counts disagree with the query plan")
    outputs = receipt.get("outputs")
    if not isinstance(outputs, dict) or len(outputs) != len(modules):
        fail("collection receipt output table is malformed")

    bits = query_manifest["parameters"]["dyadicBits"]
    values: list[collection.ParsedValue] = []
    expected_output_names: set[str] = set()
    for module, _source, expected_ids in modules:
        filename = f"{module}.out"
        expected_output_names.add(filename)
        record = outputs.get(filename)
        if not isinstance(record, dict) or set(record) != {
            "bytes",
            "byteSha256",
            "queryCount",
        }:
            fail(f"collection receipt lacks a strict record for {filename}")
        path = collection_dir / filename
        output_bytes = read_regular_file(
            path, f"collected scalar-cache output {filename}", collection.MAX_STDOUT_BYTES
        )
        if record != {
            "bytes": len(output_bytes),
            "byteSha256": sha256_bytes(output_bytes),
            "queryCount": len(expected_ids),
        }:
            fail(f"collection receipt output record drifted for {filename}")
        values.extend(collection.parse_output(output_bytes, expected_ids, bits))
    if set(outputs) != expected_output_names:
        fail("collection receipt contains unexpected output records")
    records = [value.record() for value in values]
    if sha256_bytes(canonical_json_bytes(records)) != receipt.get(
        "resultSetSha256"
    ):
        fail("collection result-set hash drifted")
    by_id = {value.cache_id: value for value in values}
    if len(by_id) != len(values):
        fail("collection repeats a cache ID")
    return receipt, by_id, data


def exact_entries(
    query_manifest: dict[str, Any], values: dict[str, collection.ParsedValue]
) -> list[CacheEntry]:
    selected = query_manifest.get("selected")
    if not isinstance(selected, list):
        fail("query manifest selected table is malformed")
    result: list[CacheEntry] = []
    for index, record in enumerate(selected):
        if not isinstance(record, dict):
            fail(f"selected[{index}] is not an object")
        identifier = record.get("cacheId")
        kind = record.get("kind")
        multiplicity = record.get("multiplicity")
        if (
            not isinstance(identifier, str)
            or identifier not in values
            or kind not in ("a", "c")
            or not isinstance(multiplicity, int)
            or multiplicity < query_manifest["parameters"][
                "cacheMultiplicityThreshold"
            ]
        ):
            fail(f"selected[{index}] has invalid proof metadata")
        s = fraction_from_record(record.get("s"), f"selected[{index}].s")
        y = fraction_from_record(record.get("y"), f"selected[{index}].y")
        key = collection.query_plan.ScalarKey(kind, s, y)
        if collection.query_plan.cache_id(
            key,
            argparse.Namespace(
                dyadic_bits=query_manifest["parameters"]["dyadicBits"],
                terms=query_manifest["parameters"]["terms"],
                authenticated_sqrt_fuel=query_manifest["parameters"]["sqrtFuel"],
                authenticated_log_fuel=query_manifest["parameters"]["logFuel"],
            ),
        ) != identifier:
            fail(f"selected[{index}] cache ID does not hash its exact key")
        result.append(
            CacheEntry(identifier, kind, s, y, multiplicity, values[identifier])
        )
    if {entry.cache_id for entry in result} != set(values):
        fail("query plan and collected values have different cache-ID sets")
    return result


def render_config(
    prefix: str,
    parameters: dict[str, Any],
    query_manifest: dict[str, Any],
    receipt: dict[str, Any],
    implementation: dict[str, object],
) -> tuple[str, str]:
    module = f"{prefix}Config"
    source = f"""import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedCornerValues

/-! Authenticated constants for the generated upper-`K` scalar cache. -/

namespace CourtadeKumar.{GENERATED_NAMESPACE}

def dyadicBits : ℕ := {parameters["dyadicBits"]}
def terms : ℕ := {parameters["terms"]}
def sqrtFuel : ℕ := {parameters["sqrtFuel"]}
def logFuel : ℕ := {parameters["logFuel"]}
def queryPlanSha256 : String := {json.dumps(query_manifest["planSha256"])}
def collectionResultSetSha256 : String :=
  {json.dumps(receipt["resultSetSha256"])}
def collectionReceiptPayloadSha256 : String :=
  {json.dumps(receipt["receiptPayloadSha256"])}
def cachedOverlaySourceSetSha256 : String :=
  {json.dumps(implementation["cachedOverlay"]["sourceSetSha256"])}

end CourtadeKumar.{GENERATED_NAMESPACE}
"""
    return module, source


def render_proof_module(
    prefix: str,
    config_module: str,
    index: int,
    entries: list[CacheEntry],
    max_rec_depth: int,
    max_heartbeats: int,
) -> tuple[str, str, list[dict[str, object]]]:
    module = f"{prefix}P{index:04d}"
    namespace = f"P{index:04d}"
    lines = [
        f"import {config_module}",
        "",
        "/-! Kernel-authenticated dyadic scalar-cache entries. -/",
        "",
        f"namespace CourtadeKumar.{GENERATED_NAMESPACE}",
        f"namespace {namespace}",
        "",
        "open LRUpperKDyadicOuterRounding",
        "open LRUpperKMidpointCoarsening",
        "",
    ]
    records: list[dict[str, object]] = []
    for entry in entries:
        tag = entry.cache_id[:16]
        value_name = f"value_{tag}"
        generated_name = f"generated_{tag}"
        covers_name = f"covers_{tag}"
        scalar = "aAutoI" if entry.kind == "a" else "cAutoI"
        exact = (
            f"LRUpperKHistoricalACValues.{scalar} terms sqrtFuel logFuel "
            f"({fraction_text(entry.s)}) ({fraction_text(entry.y)})"
        )
        lines.extend(
            [
                f"def {value_name} : RationalEnclosure :=",
                f"  {{ lower := {fraction_text(entry.value.lower)}",
                f"    upper := {fraction_text(entry.value.upper)} }}",
                "",
                f"set_option maxRecDepth {max_rec_depth} in",
                f"set_option maxHeartbeats {max_heartbeats} in",
                f"theorem {generated_name} :",
                f"    {value_name} = outerEnclosure dyadicBits ({exact}) := by",
                "  rfl'",
                "",
                f"theorem {covers_name} : Covers {value_name} ({exact}) := by",
                f"  rw [{generated_name}]",
                "  exact outerEnclosure_covers dyadicBits _",
                "",
            ]
        )
        records.append(
            {
                "cacheId": entry.cache_id,
                "module": module,
                "namespace": namespace,
                "valueName": value_name,
                "generatedName": generated_name,
                "coversName": covers_name,
                "kind": entry.kind,
                "s": [entry.s.numerator, entry.s.denominator],
                "y": [entry.y.numerator, entry.y.denominator],
                "lower": [
                    entry.value.lower.numerator,
                    entry.value.lower.denominator,
                ],
                "upper": [
                    entry.value.upper.numerator,
                    entry.value.upper.denominator,
                ],
                "multiplicity": entry.multiplicity,
            }
        )
    lines.extend(
        [
            f"end {namespace}",
            f"end CourtadeKumar.{GENERATED_NAMESPACE}",
            "",
        ]
    )
    source = "\n".join(lines)
    if source.count("  rfl'\n") != len(entries):
        fail(f"{module} did not emit exactly one kernel reduction per entry")
    return module, source, records


def validate_sources(sources: dict[str, str], expected_reductions: int) -> None:
    if not sources or len(sources) > MAX_GENERATED_MODULES:
        fail("generated scalar-cache proof module count exceeds its guard")
    combined_bytes = sum(len(source.encode("utf-8")) for source in sources.values())
    if combined_bytes > MAX_GENERATED_SOURCE_BYTES:
        fail("generated scalar-cache proof source bytes exceed their guard")
    combined = "\n".join(sources.values())
    if combined.count("  rfl'\n") != expected_reductions:
        fail("generated scalar-cache proof reduction count drifted")
    for forbidden in collection.query_plan.replay.FORBIDDEN_LEAN:
        if forbidden in combined:
            fail(f"generated scalar-cache proof contains forbidden token {forbidden!r}")
    collection.query_plan.replay.validate_generated_graph(
        sources, next(iter(sources)).split("Config")[0]
    )


def build(
    args: argparse.Namespace,
    query_manifest: dict[str, Any],
    query_manifest_bytes: bytes,
    receipt: dict[str, Any],
    receipt_bytes: bytes,
    entries: list[CacheEntry],
) -> tuple[dict[str, str], dict[str, object]]:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("scalar-cache proof generator changed before planning")
    implementation = query_manifest["implementation"]
    prefix = proof_module_prefix(args.module_prefix)
    if len({entry.cache_id[:16] for entry in entries}) != len(entries):
        fail("selected cache IDs collide at the audited 16-hex Lean-name prefix")
    config_module, config_source = render_config(
        prefix,
        query_manifest["parameters"],
        query_manifest,
        receipt,
        implementation,
    )
    sources: dict[str, str] = {config_module: config_source}
    proof_modules: list[str] = []
    entry_records: list[dict[str, object]] = []
    for index, group in enumerate(chunks(entries, args.proofs_per_module)):
        module, source, records = render_proof_module(
            prefix,
            config_module,
            index,
            group,
            args.max_rec_depth,
            args.max_heartbeats,
        )
        if module in sources:
            fail(f"generated scalar-cache proof module collision: {module}")
        sources[module] = source
        proof_modules.append(module)
        entry_records.extend(records)
    coverage, indexes = collection.query_plan.replay.add_import_fan_in(
        sources,
        prefix,
        "Coverage",
        proof_modules,
        args.max_imports_per_index,
    )
    validate_sources(sources, len(entries))
    output_hashes = {
        f"{module}.lean": sha256_bytes(source.encode("utf-8"))
        for module, source in sorted(sources.items())
    }
    manifest_core: dict[str, object] = {
        "format": FORMAT,
        "generator": {"file": SCRIPT.name, "byteSha256": SCRIPT_BYTE_SHA256},
        "proofAuthority": PROOF_AUTHORITY,
        "queryManifest": {
            "file": collection.query_plan.replay.relative_project_path(
                args.validated_query_manifest_path
            ),
            "byteSha256": sha256_bytes(query_manifest_bytes),
            "planSha256": query_manifest["planSha256"],
        },
        "collectionReceipt": {
            "file": collection.query_plan.replay.relative_project_path(
                args.validated_collection_receipt_path
            ),
            "byteSha256": sha256_bytes(receipt_bytes),
            "payloadSha256": receipt["receiptPayloadSha256"],
            "resultSetSha256": receipt["resultSetSha256"],
        },
        "implementation": implementation,
        "parameters": {
            **query_manifest["parameters"],
            "proofsPerModule": args.proofs_per_module,
            "maxImportsPerIndex": args.max_imports_per_index,
            "maxRecDepth": args.max_rec_depth,
            "maxHeartbeats": args.max_heartbeats,
            "modulePrefix": prefix,
        },
        "outputDirectory": collection.query_plan.replay.relative_project_path(
            args.validated_output_dir
        ),
        "entryCount": len(entries),
        "kernelReductionCount": len(entries),
        "proofModuleCount": len(proof_modules),
        "importIndexModules": indexes,
        "coverageModule": coverage,
        "entries": entry_records,
        "leanModuleCount": len(sources),
        "outputs": output_hashes,
    }
    plan_sha = sha256_bytes(canonical_json_bytes(manifest_core))
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("scalar-cache proof generator changed while rendering")
    if collection.query_plan.replay.bind_direct_replay_sources() != implementation[
        "directReplay"
    ] or collection.query_plan.bind_cache_overlay_sources() != implementation[
        "cachedOverlay"
    ]:
        fail("scalar-cache implementation changed while proof plan rendered")
    if read_regular_file(
        args.validated_query_manifest_path,
        "scalar-cache query manifest",
        collection.MAX_MANIFEST_BYTES,
    ) != query_manifest_bytes:
        fail("scalar-cache query manifest changed while proof plan rendered")
    if read_regular_file(
        args.validated_collection_receipt_path,
        "scalar-cache collection receipt",
        MAX_RECEIPT_BYTES,
    ) != receipt_bytes:
        fail("scalar-cache collection receipt changed while proof plan rendered")
    return sources, {**manifest_core, "planSha256": plan_sha}


def summary(manifest: dict[str, object]) -> dict[str, object]:
    return {
        "status": "validated-read-only",
        "planSha256": manifest["planSha256"],
        "queryPlanSha256": manifest["queryManifest"]["planSha256"],
        "collectionResultSetSha256": manifest["collectionReceipt"][
            "resultSetSha256"
        ],
        "outputDirectory": manifest["outputDirectory"],
        "entryCount": manifest["entryCount"],
        "kernelReductionCount": manifest["kernelReductionCount"],
        "proofModuleCount": manifest["proofModuleCount"],
        "leanModuleCount": manifest["leanModuleCount"],
        "coverageModule": manifest["coverageModule"],
    }


def validate_arguments(args: argparse.Namespace) -> None:
    if not 1 <= args.proofs_per_module <= 32:
        fail("--proofs-per-module must lie in [1,32]")
    if not 2 <= args.max_imports_per_index <= 128:
        fail("--max-imports-per-index must lie in [2,128]")
    if args.max_rec_depth <= 0 or args.max_heartbeats < 0:
        fail("Lean resource options are invalid")
    proof_module_prefix(args.module_prefix)


def prepared(
    args: argparse.Namespace,
) -> tuple[dict[str, str], dict[str, object]]:
    collection.query_plan.replay.validate_repository_location()
    validate_arguments(args)
    query_dir, _ = scratch_directory(args.query_dir, "--query-dir")
    collection_dir, _ = scratch_directory(args.collection_dir, "--collection-dir")
    output_dir, output_identity = scratch_directory(args.output_dir, "--output-dir")
    query_manifest_path = collection.query_plan.replay.project_path(
        args.query_manifest, "--query-manifest"
    )
    receipt_path = collection.query_plan.replay.project_path(
        args.collection_receipt, "--collection-receipt"
    )
    query_manifest, modules, query_bytes = load_query_manifest(
        query_dir, query_manifest_path
    )
    receipt, values, receipt_bytes = load_collection_receipt(
        receipt_path,
        collection_dir,
        query_manifest_path,
        query_bytes,
        query_manifest,
        modules,
    )
    entries = exact_entries(query_manifest, values)
    args.validated_query_manifest_path = query_manifest_path
    args.validated_collection_receipt_path = receipt_path
    args.validated_output_dir = output_dir
    args.validated_output_identity = output_identity
    return build(
        args, query_manifest, query_bytes, receipt, receipt_bytes, entries
    )


def command_plan(args: argparse.Namespace) -> None:
    _sources, manifest = prepared(args)
    print(json.dumps(summary(manifest), indent=2, sort_keys=True))


def command_generate(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        fail("refusing scalar-cache proof emission without --confirm-write")
    sources, manifest = prepared(args)
    expected = collection.query_plan.replay.supplied_hex64(
        args.expected_plan_sha256, "--expected-plan-sha256"
    )
    if expected != manifest["planSha256"]:
        fail("--expected-plan-sha256 differs from the fresh proof plan")
    directory: Path = args.validated_output_dir
    manifest_name = f"{proof_module_prefix(args.module_prefix)}Manifest.json"
    outputs = {
        collection.query_plan.replay.safe_output_path(
            directory, f"{module}.lean"
        ): source.encode("utf-8")
        for module, source in sources.items()
    }
    manifest_path = collection.query_plan.replay.safe_output_path(
        directory, manifest_name
    )
    outputs[manifest_path] = pretty_json_bytes(manifest)
    collisions = [path.name for path in outputs if path.exists() or path.is_symlink()]
    if collisions:
        fail(f"refusing to overwrite scalar-cache proof outputs: {sorted(collisions)}")
    collection.query_plan.replay.exclusive_create_all(
        directory, args.validated_output_identity, outputs
    )
    written = summary(manifest)
    written.update(
        {"status": "written", "writtenFiles": len(outputs), "manifest": manifest_name}
    )
    print(json.dumps(written, sort_keys=True))


def add_arguments(command: argparse.ArgumentParser) -> None:
    command.add_argument("--query-dir", required=True)
    command.add_argument("--query-manifest", required=True)
    command.add_argument("--collection-dir", required=True)
    command.add_argument("--collection-receipt", required=True)
    command.add_argument("--output-dir", required=True)
    command.add_argument("--proofs-per-module", type=int, default=32)
    command.add_argument("--max-imports-per-index", type=int, default=64)
    command.add_argument("--max-rec-depth", type=int, default=1_000_000)
    command.add_argument("--max-heartbeats", type=int, default=0)
    command.add_argument(
        "--module-prefix", default="AgentUpperKScalarCacheProofGenerated"
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="authenticate and plan without writing")
    add_arguments(plan)
    plan.set_defaults(handler=command_plan)
    generate = commands.add_parser(
        "generate", help="emit kernel-authenticated scalar-cache proof modules"
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
    except collection.query_plan.replay.ReplayPlanError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
