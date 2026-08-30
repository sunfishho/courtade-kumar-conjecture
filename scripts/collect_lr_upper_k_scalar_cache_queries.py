#!/usr/bin/env python3
"""Collect bounded upper-``K`` scalar-cache query output serially.

The input query plan and every generated Lean source are authenticated before
execution.  Each Lean process is run alone through the repository-local
resource-bounded checker.  Successful output is parsed strictly, written by
exclusive creation, and can be resumed after interruption.  Completed Lean
artifacts are removed by default so thousands of query modules cannot consume
unnecessary storage.

The collected rationals remain untrusted certificate data.  The final proof
stage must authenticate each one by ordinary Lean kernel reduction.
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
import subprocess
import sys
import time
from typing import Any, Iterable

import generate_lr_upper_k_scalar_cache_queries as query_plan


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
CHECKER = SCRATCH / "AgentRepoLocalLeanCheck.sh"
OUTPUT_PATTERN = re.compile(
    rb'^\("([0-9a-f]{64})", (-?[0-9]+)(?: / ([1-9][0-9]*))?, '
    rb'(-?[0-9]+)(?: / ([1-9][0-9]*))?\)$'
)
MAX_MANIFEST_BYTES = 32 * 1024 * 1024
MAX_SOURCE_BYTES = 2 * 1024 * 1024
MAX_STDOUT_BYTES = 2 * 1024 * 1024
MAX_STDERR_BYTES = 2 * 1024 * 1024
RECEIPT_FORMAT = "authenticated upper-K scalar-cache query collection v1"


@dataclass(frozen=True, slots=True)
class ParsedValue:
    cache_id: str
    lower: Fraction
    upper: Fraction

    def record(self) -> dict[str, object]:
        return {
            "cacheId": self.cache_id,
            "lower": [self.lower.numerator, self.lower.denominator],
            "upper": [self.upper.numerator, self.upper.denominator],
        }


def fail(message: str) -> None:
    raise query_plan.replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return query_plan.canonical_json_bytes(value)


def pretty_json_bytes(value: object) -> bytes:
    return query_plan.pretty_json_bytes(value)


def read_regular_file(path: Path, context: str, maximum: int) -> bytes:
    return query_plan.replay.read_regular_file(path, context, maximum)


def scratch_directory(raw: str, option: str) -> tuple[Path, tuple[int, int]]:
    path = query_plan.replay.project_path(raw, option)
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


def strict_manifest(path: Path, query_dir: Path) -> dict[str, Any]:
    data = read_regular_file(path, "scalar-cache query manifest", MAX_MANIFEST_BYTES)
    try:
        manifest = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse scalar-cache query manifest: {error}")
    if not isinstance(manifest, dict):
        fail("scalar-cache query manifest must be a JSON object")
    plan_sha = manifest.get("planSha256")
    if not isinstance(plan_sha, str) or re.fullmatch(r"[0-9a-f]{64}", plan_sha) is None:
        fail("scalar-cache query manifest has an invalid planSha256")
    core = dict(manifest)
    del core["planSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != plan_sha:
        fail("scalar-cache query manifest plan hash is invalid")
    if manifest.get("format") != query_plan.FORMAT:
        fail("scalar-cache query manifest format drifted")
    expected_directory = query_plan.replay.relative_project_path(query_dir)
    if manifest.get("outputDirectory") != expected_directory:
        fail("query directory differs from the manifest outputDirectory")

    generator = manifest.get("generator")
    if not isinstance(generator, dict):
        fail("query manifest generator record is missing")
    expected_generator = {
        "file": query_plan.SCRIPT.name,
        "byteSha256": query_plan.SCRIPT_BYTE_SHA256,
        "directReplayGeneratorFile": query_plan.replay.SCRIPT.name,
        "directReplayGeneratorByteSha256": query_plan.replay.SCRIPT_BYTE_SHA256,
    }
    if generator != expected_generator:
        fail("query manifest is not bound to the current committed generators")
    implementation = manifest.get("implementation")
    if not isinstance(implementation, dict) or implementation != {
        "directReplay": query_plan.replay.bind_direct_replay_sources(),
        "cachedOverlay": query_plan.bind_cache_overlay_sources(),
    }:
        fail("query manifest implementation binding is stale")
    return manifest


def expected_modules(
    manifest: dict[str, Any], query_dir: Path
) -> list[tuple[str, Path, list[str]]]:
    outputs = manifest.get("outputs")
    queries = manifest.get("queries")
    selected = manifest.get("selected")
    if not isinstance(outputs, dict) or not isinstance(queries, list) or not isinstance(
        selected, list
    ):
        fail("query manifest output tables are malformed")
    if len(outputs) != manifest.get("queryModuleCount") or len(queries) != len(outputs):
        fail("query manifest module counts disagree")
    by_module: dict[str, list[tuple[int, str]]] = {}
    seen_ids: set[str] = set()
    for record in selected:
        if not isinstance(record, dict):
            fail("query manifest selected entry is not an object")
        identifier = record.get("cacheId")
        module = record.get("queryModule")
        index = record.get("queryIndex")
        if (
            not isinstance(identifier, str)
            or re.fullmatch(r"[0-9a-f]{64}", identifier) is None
            or not isinstance(module, str)
            or not isinstance(index, int)
            or index < 0
        ):
            fail("query manifest selected entry has invalid addressing")
        if identifier in seen_ids:
            fail("query manifest repeats a selected cache ID")
        seen_ids.add(identifier)
        by_module.setdefault(module, []).append((index, identifier))
    if len(selected) != manifest.get("selectedScalarKeys"):
        fail("query manifest selected-key count disagrees")

    result: list[tuple[str, Path, list[str]]] = []
    seen_modules: set[str] = set()
    for query in queries:
        if not isinstance(query, dict):
            fail("query manifest module record is malformed")
        module = query.get("module")
        count = query.get("queryCount")
        if not isinstance(module, str) or not isinstance(count, int) or count <= 0:
            fail("query manifest module identity/count is invalid")
        if module in seen_modules:
            fail("query manifest repeats a module")
        seen_modules.add(module)
        filename = f"{module}.lean"
        expected_hash = outputs.get(filename)
        if not isinstance(expected_hash, str) or re.fullmatch(
            r"[0-9a-f]{64}", expected_hash
        ) is None:
            fail(f"query manifest lacks an output hash for {filename}")
        source = query_dir / filename
        source_bytes = read_regular_file(source, f"query source {filename}", MAX_SOURCE_BYTES)
        if sha256_bytes(source_bytes) != expected_hash:
            fail(f"query source hash drifted for {filename}")
        entries = sorted(by_module.get(module, []))
        if [index for index, _identifier in entries] != list(range(count)):
            fail(f"query indexes are not contiguous for {module}")
        ids = [identifier for _index, identifier in entries]
        if ids[0] != query.get("firstCacheId") or ids[-1] != query.get(
            "lastCacheId"
        ):
            fail(f"query endpoint IDs drifted for {module}")
        result.append((module, source, ids))
    if seen_modules != set(by_module) or set(outputs) != {
        f"{module}.lean" for module in seen_modules
    }:
        fail("query manifest modules, selected entries, and outputs disagree")
    return result


def parse_rational(numerator: bytes, denominator: bytes | None) -> Fraction:
    return Fraction(int(numerator), int(denominator) if denominator is not None else 1)


def parse_output(data: bytes, expected_ids: list[str], bits: int) -> list[ParsedValue]:
    if len(data) > MAX_STDOUT_BYTES:
        fail("query stdout exceeds the hard byte guard")
    if not data.endswith(b"\n"):
        fail("query stdout is not newline terminated")
    lines = data.splitlines()
    if len(lines) != len(expected_ids):
        fail("query stdout line count differs from the manifest")
    values: list[ParsedValue] = []
    maximum_denominator = 1 << bits
    for index, (line, expected_id) in enumerate(zip(lines, expected_ids, strict=True)):
        match = OUTPUT_PATTERN.fullmatch(line)
        if match is None:
            fail(f"query stdout line {index} has an unexpected Lean representation")
        identifier = match.group(1).decode("ascii")
        if identifier != expected_id:
            fail(f"query stdout ID order drifted at line {index}")
        lower = parse_rational(match.group(2), match.group(3))
        upper = parse_rational(match.group(4), match.group(5))
        if lower > upper:
            fail(f"query stdout interval is reversed for {identifier}")
        for endpoint in (lower, upper):
            denominator = endpoint.denominator
            if (
                denominator > maximum_denominator
                or denominator & (denominator - 1) != 0
            ):
                fail(f"query stdout is not a {bits}-bit dyadic for {identifier}")
        values.append(ParsedValue(identifier, lower, upper))
    return values


def exclusive_write(
    path: Path, data: bytes, expected_directory_identity: tuple[int, int]
) -> None:
    query_plan.replay.exclusive_create_all(
        path.parent, expected_directory_identity, {path: data}
    )


def remove_lean_artifacts(source: Path) -> None:
    for suffix in (".olean", ".ilean"):
        artifact = source.with_suffix(suffix)
        try:
            metadata = artifact.lstat()
        except FileNotFoundError:
            continue
        if stat.S_ISREG(metadata.st_mode) and not stat.S_ISLNK(metadata.st_mode):
            artifact.unlink()
        else:
            fail(f"refusing to remove non-regular Lean artifact {artifact.name}")


def validate_existing_output(
    path: Path, expected_ids: list[str], bits: int
) -> tuple[bytes, list[ParsedValue]]:
    data = read_regular_file(path, f"collected output {path.name}", MAX_STDOUT_BYTES)
    return data, parse_output(data, expected_ids, bits)


def collect(args: argparse.Namespace) -> None:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("collector changed before execution")
    query_plan.replay.validate_repository_location()
    query_dir, _query_identity = scratch_directory(args.query_dir, "--query-dir")
    output_dir, output_identity = scratch_directory(args.output_dir, "--output-dir")
    manifest_path = query_plan.replay.project_path(
        args.query_manifest, "--query-manifest"
    )
    if manifest_path.parent != query_dir:
        fail("--query-manifest must be directly inside --query-dir")
    manifest = strict_manifest(manifest_path, query_dir)
    modules = expected_modules(manifest, query_dir)
    parameters = manifest.get("parameters")
    if not isinstance(parameters, dict) or not isinstance(
        parameters.get("dyadicBits"), int
    ):
        fail("query manifest dyadic precision is malformed")
    bits = parameters["dyadicBits"]
    if args.max_modules < 1:
        fail("--max-modules must be positive")
    if args.timeout_seconds < 1:
        fail("--timeout-seconds must be positive")
    if not CHECKER.is_file() or CHECKER.is_symlink():
        fail("repository-local Lean checker is missing or not a regular file")
    checker_bytes = read_regular_file(CHECKER, "repository-local Lean checker", 64_000)

    output_metadata = output_dir.stat()
    if (output_metadata.st_dev, output_metadata.st_ino) != output_identity:
        fail("--output-dir identity changed before collection")
    processed = 0
    reused = 0
    started = time.monotonic()
    for ordinal, (module, source, expected_ids) in enumerate(modules):
        output = output_dir / f"{module}.out"
        if output.exists() or output.is_symlink():
            _data, _values = validate_existing_output(output, expected_ids, bits)
            reused += 1
            if not args.keep_lean_artifacts:
                remove_lean_artifacts(source)
            continue
        if processed >= args.max_modules:
            break
        relative_source = source.relative_to(REPOSITORY).as_posix()
        module_started = time.monotonic()
        try:
            result = subprocess.run(
                ["/bin/zsh", str(CHECKER), relative_source],
                cwd=REPOSITORY,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                timeout=args.timeout_seconds,
            )
        except subprocess.TimeoutExpired as error:
            fail(f"Lean query timed out for {module}: {error}")
        if len(result.stderr) > MAX_STDERR_BYTES:
            fail(f"Lean query stderr exceeded its guard for {module}")
        if result.returncode != 0:
            diagnostic = result.stderr.decode("utf-8", errors="replace")[-4000:]
            fail(f"Lean query failed for {module}: {diagnostic}")
        parse_output(result.stdout, expected_ids, bits)
        exclusive_write(output, result.stdout, output_identity)
        if not args.keep_lean_artifacts:
            remove_lean_artifacts(source)
        processed += 1
        elapsed = time.monotonic() - module_started
        completed = reused + processed
        print(
            json.dumps(
                {
                    "status": "collected",
                    "module": module,
                    "ordinal": ordinal,
                    "completedModules": completed,
                    "totalModules": len(modules),
                    "queries": len(expected_ids),
                    "seconds": round(elapsed, 3),
                },
                sort_keys=True,
            ),
            flush=True,
        )

    all_outputs: dict[str, dict[str, object]] = {}
    all_values: list[dict[str, object]] = []
    missing: list[str] = []
    for module, _source, expected_ids in modules:
        output = output_dir / f"{module}.out"
        if not output.exists() or output.is_symlink():
            missing.append(module)
            continue
        data, values = validate_existing_output(output, expected_ids, bits)
        all_outputs[output.name] = {
            "bytes": len(data),
            "byteSha256": sha256_bytes(data),
            "queryCount": len(values),
        }
        all_values.extend(value.record() for value in values)

    if missing:
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

    if len(all_values) != manifest["selectedScalarKeys"]:
        fail("complete collection value count disagrees with query manifest")
    receipt_core: dict[str, object] = {
        "format": RECEIPT_FORMAT,
        "collector": {"file": SCRIPT.name, "byteSha256": SCRIPT_BYTE_SHA256},
        "checker": {"file": CHECKER.name, "byteSha256": sha256_bytes(checker_bytes)},
        "proofAuthority": (
            "none: collected values remain untrusted until ordinary Lean kernel "
            "reductions authenticate them"
        ),
        "queryManifest": {
            "file": query_plan.replay.relative_project_path(manifest_path),
            "byteSha256": sha256_bytes(
                read_regular_file(
                    manifest_path, "scalar-cache query manifest", MAX_MANIFEST_BYTES
                )
            ),
            "planSha256": manifest["planSha256"],
        },
        "moduleCount": len(modules),
        "valueCount": len(all_values),
        "resultSetSha256": sha256_bytes(canonical_json_bytes(all_values)),
        "outputs": dict(sorted(all_outputs.items())),
    }
    receipt = {
        **receipt_core,
        "receiptPayloadSha256": sha256_bytes(canonical_json_bytes(receipt_core)),
    }
    receipt_name = f"{parameters['modulePrefix']}CollectionReceipt.json"
    receipt_path = output_dir / receipt_name
    rendered = pretty_json_bytes(receipt)
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("collector changed during execution")
    if read_regular_file(CHECKER, "repository-local Lean checker", 64_000) != checker_bytes:
        fail("repository-local Lean checker changed during execution")
    if receipt_path.exists() or receipt_path.is_symlink():
        existing = read_regular_file(
            receipt_path, "scalar-cache collection receipt", MAX_MANIFEST_BYTES
        )
        if existing != rendered:
            fail("existing complete collection receipt differs from fresh receipt")
    else:
        exclusive_write(receipt_path, rendered, output_identity)
    print(
        json.dumps(
            {
                "status": "complete",
                "moduleCount": len(modules),
                "valueCount": len(all_values),
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
    result.add_argument("--timeout-seconds", type=int, default=900)
    result.add_argument("--keep-lean-artifacts", action="store_true")
    return result


def main(argv: Iterable[str] | None = None) -> None:
    args = parser().parse_args(list(argv) if argv is not None else None)
    collect(args)


if __name__ == "__main__":
    try:
        main()
    except query_plan.replay.ReplayPlanError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
