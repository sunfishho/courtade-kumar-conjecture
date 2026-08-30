#!/usr/bin/env python3
"""Generate all v3 fast point-cache values without running Lean.

This authenticated driver consumes a threshold-one v3 fast-point query
manifest, checks the manifest and every generated query source through the
strict collector API, evaluates the exact closed rational program with
``evaluate_lr_upper_k_fast_points``, and emits the same twenty atomic fields
as the Lean ``#eval`` query.

The resulting data remain untrusted.  The receipt explicitly records that no
Lean process was used and binds the exact evaluator source, driver source,
certificate scheme, query schema, and numerical parameters.  It deliberately
uses the existing collector receipt format and canonical result-set hash so
the downstream proof generator can consume the result immediately.  Each
generated Lean proof then authenticates its literal certificate and outer
enclosures with ordinary kernel reduction.

Output files are created exclusively and never overwritten.  Existing shards
are freshly recomputed and reused only on byte equality, so interrupted runs
are deterministic and safely resumable.

Production invocation from the repository root::

    python3 -B scripts/generate_lr_upper_k_fast_point_cache_values.py \
      --query-dir .lake/scratch/GeneratedUpperKFastPointCacheQueriesV3 \
      --query-manifest \
        .lake/scratch/GeneratedUpperKFastPointCacheQueriesV3/\
AgentUpperKFastPointCacheQueryGeneratedManifest.json \
      --output-dir .lake/scratch/GeneratedUpperKFastPointCacheValuesV3 \
      --confirm-write
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
from typing import Any, Iterable


sys.dont_write_bytecode = True

import collect_lr_upper_k_fast_point_cache_queries as collection
import evaluate_lr_upper_k_fast_points as evaluator


SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
REQUIRED_POINT_BITS = 40
REQUIRED_LOG_BITS = 40
REQUIRED_SQRT_BITS = 40
REQUIRED_TERMS = 12
REQUIRED_LOG_FUEL = 48
REQUIRED_CACHE_THRESHOLD = 1
EXECUTION_MODE = "pure Python fractions.Fraction; no Lean process executed"
PROOF_AUTHORITY = (
    "none: collected values remain untrusted until ordinary Lean kernel "
    "reductions authenticate them"
)


def fail(message: str) -> None:
    raise collection.query_plan.replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return collection.canonical_json_bytes(value)


def pretty_json_bytes(value: object) -> bytes:
    return collection.pretty_json_bytes(value)


def exact_parameters(manifest: dict[str, Any]) -> dict[str, Any]:
    parameters = collection.strict_parameters(manifest)
    expected = {
        "pointDyadicBits": REQUIRED_POINT_BITS,
        "logDyadicBits": REQUIRED_LOG_BITS,
        "sqrtDyadicBits": REQUIRED_SQRT_BITS,
        "terms": REQUIRED_TERMS,
        "logFuel": REQUIRED_LOG_FUEL,
        "cacheMultiplicityThreshold": REQUIRED_CACHE_THRESHOLD,
    }
    for key, value in expected.items():
        if parameters.get(key) != value:
            fail(f"authenticated pure point evaluation requires {key} = {value}")
    if parameters.get("certificateScheme") != collection.EXPECTED_CERTIFICATE_SCHEME:
        fail("pure point evaluator certificate scheme drifted")
    if parameters.get("cacheKeySchema") != collection.EXPECTED_CACHE_KEY_SCHEMA:
        fail("pure point evaluator cache-key schema drifted")
    if collection.QUERY_COLUMNS != evaluator.ROUNDED_LOG_COLUMNS:
        fail("pure evaluator and strict collector disagree on the twenty fields")
    if collection.query_plan.QUERY_ROW_SCHEMA != collection.EXPECTED_QUERY_ROW_SCHEMA:
        fail("pure evaluator and query planner disagree on v3 row identity")
    return parameters


def authenticate_complete_threshold_one_plan(manifest: dict[str, Any]) -> None:
    selected = manifest.get("selectedPointKeys")
    unique = manifest.get("uniquePointKeys")
    fallback = manifest.get("localFallbackPointOccurrences")
    materializations = manifest.get("resultingPointMaterializations")
    if (
        not isinstance(selected, int)
        or isinstance(selected, bool)
        or selected <= 0
        or selected != unique
        or fallback != 0
        or materializations != selected
    ):
        fail(
            "threshold-one fast point plan must select every unique point with "
            "no local fallback materializations"
        )


def render_module(
    expected: list[collection.ExpectedPoint], parameters: dict[str, Any]
) -> bytes:
    rows: list[bytes] = []
    for point in expected:
        value = evaluator.evaluate_point(
            point.z,
            point_bits=parameters["pointDyadicBits"],
            terms=parameters["terms"],
            sqrt_bits=parameters["sqrtDyadicBits"],
            log_fuel=parameters["logFuel"],
        )
        rows.append(
            evaluator.render_row(
                point.cache_id, value, evaluator.ROUNDED_LOG_COLUMNS
            )
        )
    data = b"".join(rows)
    # Reparse with the exact downstream grammar before any byte is persisted.
    collection.parse_output(data, expected, parameters)
    return data


def evaluator_record(parameters: dict[str, Any]) -> dict[str, object]:
    return {
        "driver": {"file": SCRIPT.name, "byteSha256": SCRIPT_BYTE_SHA256},
        "exactEvaluator": {
            "file": evaluator.SCRIPT.name,
            "byteSha256": evaluator.SCRIPT_BYTE_SHA256,
        },
        "executionMode": EXECUTION_MODE,
        "queryRowSchema": collection.EXPECTED_QUERY_ROW_SCHEMA,
        "cacheKeySchema": collection.EXPECTED_CACHE_KEY_SCHEMA,
        "certificateScheme": collection.EXPECTED_CERTIFICATE_SCHEME,
        "parameters": {
            "pointDyadicBits": parameters["pointDyadicBits"],
            "logDyadicBits": parameters["logDyadicBits"],
            "sqrtDyadicBits": parameters["sqrtDyadicBits"],
            "terms": parameters["terms"],
            "logFuel": parameters["logFuel"],
            "cacheMultiplicityThreshold": parameters[
                "cacheMultiplicityThreshold"
            ],
        },
        "leanCompatibilityFixture": {
            "z": [549153, 549755813888],
            "pointDyadicBits": 40,
            "logDyadicBits": 40,
            "sqrtDyadicBits": 40,
            "terms": 12,
            "logFuel": 48,
            "status": "exact evaluator self-check passed against saved Lean #eval",
        },
    }


def generate(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        fail("refusing pure fast-point value generation without --confirm-write")
    if args.max_modules < 1:
        fail("--max-modules must be positive")
    if args.progress_every < 1:
        fail("--progress-every must be positive")
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("pure fast-point value driver changed before execution")
    if sha256_bytes(evaluator.SCRIPT.read_bytes()) != evaluator.SCRIPT_BYTE_SHA256:
        fail("exact Fraction evaluator changed before execution")
    evaluator.self_check()
    collection.query_plan.replay.validate_repository_location()

    query_dir, _query_identity = collection.scratch_directory(
        args.query_dir, "--query-dir"
    )
    output_dir, output_identity = collection.scratch_directory(
        args.output_dir, "--output-dir"
    )
    manifest_path = collection.query_plan.replay.project_path(
        args.query_manifest, "--query-manifest"
    )
    if manifest_path.parent != query_dir:
        fail("--query-manifest must be directly inside --query-dir")
    manifest = collection.strict_manifest(manifest_path, query_dir)
    manifest_bytes = collection.read_regular_file(
        manifest_path,
        "fast point-cache query manifest",
        collection.MAX_MANIFEST_BYTES,
    )
    try:
        if json.loads(manifest_bytes) != manifest:
            fail("fast point query manifest changed during authentication")
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot reparse fast point query manifest: {error}")
    parameters = exact_parameters(manifest)
    authenticate_complete_threshold_one_plan(manifest)
    modules = collection.expected_modules(manifest, query_dir)

    if not collection.CHECKER.is_file() or collection.CHECKER.is_symlink():
        fail("collector-compatible checker identity is missing")
    checker_bytes = collection.read_regular_file(
        collection.CHECKER,
        "collector-compatible repository-local checker",
        collection.MAX_CHECKER_BYTES,
    )
    output_metadata = output_dir.stat()
    if (output_metadata.st_dev, output_metadata.st_ino) != output_identity:
        fail("--output-dir identity changed before value generation")
    receipt_name = f"{parameters['modulePrefix']}CollectionReceipt.json"
    expected_output_names = {
        f"{module}.out" for module, _source, _expected in modules
    }
    collection.reject_unexpected_output_files(
        output_dir, expected_output_names, receipt_name
    )

    started = time.monotonic()
    processed = 0
    reused = 0
    for ordinal, (module, _source, expected) in enumerate(modules):
        output = output_dir / f"{module}.out"
        exists = output.exists() or output.is_symlink()
        if not exists and processed >= args.max_modules:
            continue
        module_started = time.monotonic()
        data = render_module(expected, parameters)
        if exists:
            existing = collection.read_regular_file(
                output,
                f"existing pure fast point output {output.name}",
                collection.MAX_STDOUT_BYTES,
            )
            if existing != data:
                fail(f"existing output differs from exact evaluation: {output.name}")
            reused += 1
        else:
            collection.exclusive_write(output, data, output_identity)
            processed += 1
        completed = reused + processed
        if (
            completed == 1
            or completed % args.progress_every == 0
            or completed == len(modules)
        ):
            print(
                json.dumps(
                    {
                        "status": "reused" if exists else "generated",
                        "module": module,
                        "ordinal": ordinal,
                        "completedModules": completed,
                        "totalModules": len(modules),
                        "values": len(expected),
                        "moduleSeconds": round(
                            time.monotonic() - module_started, 3
                        ),
                        "elapsedSeconds": round(time.monotonic() - started, 3),
                    },
                    sort_keys=True,
                ),
                flush=True,
            )

    missing = [
        module
        for module, _source, _expected in modules
        if not (output_dir / f"{module}.out").is_file()
        or (output_dir / f"{module}.out").is_symlink()
    ]
    if missing:
        receipt_path = output_dir / receipt_name
        if receipt_path.exists() or receipt_path.is_symlink():
            fail("a complete receipt exists while pure value shards are missing")
        print(
            json.dumps(
                {
                    "status": "partial",
                    "newModules": processed,
                    "reusedModules": reused,
                    "completedModules": len(modules) - len(missing),
                    "remainingModules": len(missing),
                    "elapsedSeconds": round(time.monotonic() - started, 3),
                },
                sort_keys=True,
            ),
            flush=True,
        )
        return

    result_hasher = hashlib.sha256()
    result_hasher.update(b"[")
    first_record = True
    value_count = 0
    seen_ids: set[str] = set()
    outputs: dict[str, dict[str, object]] = {}
    for module, _source, expected in modules:
        output = output_dir / f"{module}.out"
        data, values = collection.validate_existing_output(
            output, expected, parameters
        )
        for value in values:
            if value.cache_id in seen_ids:
                fail("complete pure fast point result repeats a cache ID")
            seen_ids.add(value.cache_id)
        first_record, added = collection.update_result_set_hash(
            result_hasher, values, first_record
        )
        value_count += added
        outputs[output.name] = {
            "bytes": len(data),
            "byteSha256": sha256_bytes(data),
            "queryCount": len(values),
        }
    result_hasher.update(b"]")
    if value_count != manifest["selectedPointKeys"] or len(seen_ids) != value_count:
        fail("complete pure fast point value count disagrees with the manifest")

    receipt_core: dict[str, object] = {
        "format": collection.RECEIPT_FORMAT,
        # This names the strict parser/receipt contract used to validate every
        # row.  The separate evaluator record identifies how bytes were made.
        "collector": {
            "file": collection.SCRIPT.name,
            "byteSha256": collection.SCRIPT_BYTE_SHA256,
        },
        # Retained for immediate compatibility with the proof generator.  The
        # evaluator record makes explicit that this checker was not executed.
        "checker": {
            "file": collection.CHECKER.name,
            "byteSha256": sha256_bytes(checker_bytes),
        },
        "evaluator": evaluator_record(parameters),
        "proofAuthority": PROOF_AUTHORITY,
        "queryManifest": {
            "file": collection.query_plan.replay.relative_project_path(
                manifest_path
            ),
            "byteSha256": sha256_bytes(manifest_bytes),
            "planSha256": manifest["planSha256"],
        },
        "certificateScheme": parameters["certificateScheme"],
        "moduleCount": len(modules),
        "valueCount": value_count,
        "resultSetHashAlgorithm": collection.RESULT_SET_HASH_ALGORITHM,
        "resultSetSha256": result_hasher.hexdigest(),
        "outputs": dict(sorted(outputs.items())),
    }
    receipt = {
        **receipt_core,
        "receiptPayloadSha256": sha256_bytes(canonical_json_bytes(receipt_core)),
    }
    rendered = pretty_json_bytes(receipt)
    receipt_path = output_dir / receipt_name

    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("pure fast-point value driver changed during execution")
    if sha256_bytes(evaluator.SCRIPT.read_bytes()) != evaluator.SCRIPT_BYTE_SHA256:
        fail("exact Fraction evaluator changed during execution")
    if sha256_bytes(collection.SCRIPT.read_bytes()) != collection.SCRIPT_BYTE_SHA256:
        fail("strict fast point collector changed during pure evaluation")
    if collection.read_regular_file(
        manifest_path,
        "fast point-cache query manifest",
        collection.MAX_MANIFEST_BYTES,
    ) != manifest_bytes:
        fail("fast point query manifest changed during pure evaluation")
    if manifest["implementation"] != {
        "directReplay": collection.query_plan.replay.bind_direct_replay_sources(),
        "fastPointCache": collection.query_plan.bind_fast_point_sources(),
    }:
        fail("fast point implementation changed during pure evaluation")
    if collection.read_regular_file(
        collection.CHECKER,
        "collector-compatible repository-local checker",
        collection.MAX_CHECKER_BYTES,
    ) != checker_bytes:
        fail("collector-compatible checker identity changed during evaluation")

    if receipt_path.exists() or receipt_path.is_symlink():
        existing = collection.read_regular_file(
            receipt_path,
            "existing pure fast point collection receipt",
            collection.MAX_MANIFEST_BYTES,
        )
        if existing != rendered:
            fail("existing complete receipt differs from pure evaluation")
    else:
        collection.exclusive_write(receipt_path, rendered, output_identity)
    print(
        json.dumps(
            {
                "status": "complete",
                "executionMode": EXECUTION_MODE,
                "moduleCount": len(modules),
                "valueCount": value_count,
                "resultSetSha256": receipt["resultSetSha256"],
                "receiptPayloadSha256": receipt["receiptPayloadSha256"],
                "receipt": receipt_name,
                "elapsedSeconds": round(time.monotonic() - started, 3),
            },
            sort_keys=True,
        ),
        flush=True,
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--query-dir", required=True)
    result.add_argument("--query-manifest", required=True)
    result.add_argument("--output-dir", required=True)
    result.add_argument("--max-modules", type=int, default=20_000)
    result.add_argument("--progress-every", type=int, default=50)
    result.add_argument("--confirm-write", action="store_true")
    return result


def main(argv: Iterable[str] | None = None) -> None:
    generate(parser().parse_args(list(argv) if argv is not None else None))


if __name__ == "__main__":
    try:
        main()
    except collection.query_plan.replay.ReplayPlanError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
