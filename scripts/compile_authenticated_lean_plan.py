#!/usr/bin/env python3
"""Compile a hash-authenticated generated Lean plan serially and resumably.

The plan manifest's canonical ``planSha256`` and every declared Lean source
hash are checked before execution.  Generated imports are topologically
ordered.  Exactly one caller-supplied resource-bounded checker process runs at
a time.  Each successful module receives an exclusive sidecar binding its
source, checker, requested artifact mode, generated dependencies, and artifact
hashes; valid sidecars are reused after interruption.  The default ``pair``
mode requires both ``.olean`` and ``.ilean``.  The explicit ``olean-only`` mode
requires ``.olean`` and rejects a checker that also emits ``.ilean``.  The
selected mode is exported to the checker as ``CK_ARTIFACT_MODE``.  Checker
diagnostics are captured in scratch-local temporary files, size-checked, and
only read through a bounded failure tail.

This tool does not add proof authority.  Lean's kernel checks the source, and
the sidecars only make the local compilation workflow resumable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any, BinaryIO, Iterable

import generate_lr_upper_k_historical_patched_replay as replay


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
FORMAT = "authenticated generated Lean compilation receipt v2"
SIDECAR_FORMAT = "authenticated generated Lean module compilation v2"
ARTIFACT_MODES = ("pair", "olean-only")
MAX_MANIFEST_BYTES = 256 * 1024 * 1024
MAX_SOURCE_BYTES = 2 * 1024 * 1024
MAX_CHECKER_BYTES = 128 * 1024
MAX_DIAGNOSTIC_BYTES = 4 * 1024 * 1024
IMPORT_PATTERN = re.compile(r"^import\s+(\S+)\s*$", re.MULTILINE)


def fail(message: str) -> None:
    raise replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return replay.canonical_json_bytes(value)


def pretty_json_bytes(value: object) -> bytes:
    return replay.pretty_json_bytes(value)


def read_regular_file(path: Path, context: str, maximum: int) -> bytes:
    return replay.read_regular_file(path, context, maximum)


def scratch_directory(raw: str, option: str) -> tuple[Path, tuple[int, int]]:
    path = replay.project_path(raw, option)
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


def load_plan(
    manifest_path: Path, source_dir: Path, supplied_plan_sha: str
) -> tuple[dict[str, Any], bytes, dict[str, bytes]]:
    if manifest_path.parent != source_dir:
        fail("--manifest must be directly inside --source-dir")
    manifest_bytes = read_regular_file(
        manifest_path, "generated Lean plan manifest", MAX_MANIFEST_BYTES
    )
    try:
        manifest = json.loads(manifest_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse generated Lean plan manifest: {error}")
    if not isinstance(manifest, dict):
        fail("generated Lean plan manifest must be a JSON object")
    plan_sha = manifest.get("planSha256")
    if plan_sha != replay.supplied_hex64(supplied_plan_sha, "--plan-sha256"):
        fail("generated Lean plan hash differs from --plan-sha256")
    core = dict(manifest)
    if "planSha256" not in core:
        fail("generated Lean plan lacks planSha256")
    del core["planSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != plan_sha:
        fail("generated Lean plan hash does not authenticate its content")
    if manifest.get("outputDirectory") != replay.relative_project_path(source_dir):
        fail("generated Lean plan outputDirectory differs from --source-dir")
    outputs = manifest.get("outputs")
    if not isinstance(outputs, dict) or not outputs:
        fail("generated Lean plan has no output table")
    sources: dict[str, bytes] = {}
    for filename, expected_hash in outputs.items():
        if (
            not isinstance(filename, str)
            or Path(filename).name != filename
            or not filename.endswith(".lean")
            or not isinstance(expected_hash, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected_hash) is None
        ):
            fail("generated Lean plan output record is invalid")
        data = read_regular_file(
            source_dir / filename, f"generated Lean source {filename}", MAX_SOURCE_BYTES
        )
        if sha256_bytes(data) != expected_hash:
            fail(f"generated Lean source hash drifted for {filename}")
        sources[filename[:-5]] = data
    if manifest.get("leanModuleCount") != len(sources):
        fail("generated Lean plan module count disagrees with its outputs")
    return manifest, manifest_bytes, sources


def dependency_graph(sources: dict[str, bytes]) -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    modules = set(sources)
    for module, data in sources.items():
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as error:
            fail(f"generated Lean source {module} is not UTF-8: {error}")
        dependencies = [
            dependency
            for dependency in IMPORT_PATTERN.findall(text)
            if dependency in modules
        ]
        if len(dependencies) != len(set(dependencies)):
            fail(f"generated module {module} repeats an internal import")
        graph[module] = dependencies
    return graph


def topological_order(graph: dict[str, list[str]]) -> list[str]:
    state: dict[str, int] = {}
    result: list[str] = []

    def visit(module: str) -> None:
        status = state.get(module, 0)
        if status == 1:
            fail(f"generated import cycle reaches {module}")
        if status == 2:
            return
        state[module] = 1
        for dependency in graph[module]:
            visit(dependency)
        state[module] = 2
        result.append(module)

    for module in sorted(graph):
        visit(module)
    if len(result) != len(graph) or len(set(result)) != len(result):
        fail("generated topological ordering lost or repeated a module")
    return result


def artifact_record(path: Path, context: str) -> dict[str, object]:
    data = read_regular_file(path, context, 2 * 1024 * 1024 * 1024)
    if not data:
        fail(f"{context} is empty")
    return {"file": path.name, "bytes": len(data), "byteSha256": sha256_bytes(data)}


def file_size(handle: BinaryIO) -> int:
    return os.fstat(handle.fileno()).st_size


def read_file_tail(handle: BinaryIO, maximum: int) -> bytes:
    size = file_size(handle)
    handle.seek(max(0, size - maximum))
    return handle.read(maximum)


def artifact_kinds(artifact_mode: str) -> tuple[str, ...]:
    if artifact_mode == "pair":
        return ("olean", "ilean")
    if artifact_mode == "olean-only":
        return ("olean",)
    fail(f"unsupported artifact mode {artifact_mode!r}")


def forbidden_artifact_kinds(artifact_mode: str) -> tuple[str, ...]:
    if artifact_mode == "olean-only":
        return ("ilean",)
    if artifact_mode == "pair":
        return ()
    fail(f"unsupported artifact mode {artifact_mode!r}")


def module_artifact_records(
    source_dir: Path, module: str, artifact_mode: str
) -> dict[str, object]:
    return {
        kind: artifact_record(
            source_dir / f"{module}.{kind}", f"{module} .{kind}"
        )
        for kind in artifact_kinds(artifact_mode)
    }


def sidecar_path(source_dir: Path, module: str) -> Path:
    return source_dir / f"{module}.compiled.json"


def compilation_receipt_name(manifest_stem: str, artifact_mode: str) -> str:
    artifact_kinds(artifact_mode)
    mode_label = "" if artifact_mode == "pair" else "OleanOnly"
    return f"{manifest_stem}{mode_label}CompilationReceipt.json"


def expected_sidecar_core(
    module: str,
    source_hash: str,
    checker_path: Path,
    checker_hash: str,
    extra_paths: list[str],
    dependency_records: dict[str, dict[str, object]],
    source_dir: Path,
    artifact_mode: str,
) -> dict[str, object]:
    return {
        "format": SIDECAR_FORMAT,
        "compiler": {"file": SCRIPT.name, "byteSha256": SCRIPT_BYTE_SHA256},
        "artifactMode": artifact_mode,
        "module": module,
        "source": {"file": f"{module}.lean", "byteSha256": source_hash},
        "checker": {
            "file": replay.relative_project_path(checker_path),
            "byteSha256": checker_hash,
        },
        "extraLeanPath": extra_paths,
        "generatedDependencies": dependency_records,
        "artifacts": module_artifact_records(source_dir, module, artifact_mode),
    }


def validate_sidecar(
    path: Path,
    module: str,
    source_hash: str,
    checker_path: Path,
    checker_hash: str,
    extra_paths: list[str],
    dependency_records: dict[str, dict[str, object]],
    source_dir: Path,
    artifact_mode: str,
) -> tuple[bool, dict[str, object] | None]:
    if not path.exists() and not path.is_symlink():
        return False, None
    data = read_regular_file(path, f"compilation sidecar {path.name}", 2 * 1024 * 1024)
    try:
        document = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False, None
    if not isinstance(document, dict) or set(document) != {
        "format",
        "compiler",
        "artifactMode",
        "module",
        "source",
        "checker",
        "extraLeanPath",
        "generatedDependencies",
        "artifacts",
        "sidecarPayloadSha256",
    }:
        return False, None
    payload = document.get("sidecarPayloadSha256")
    core = dict(document)
    del core["sidecarPayloadSha256"]
    if not isinstance(payload, str) or sha256_bytes(canonical_json_bytes(core)) != payload:
        return False, None
    for kind in forbidden_artifact_kinds(artifact_mode):
        forbidden_path = source_dir / f"{module}.{kind}"
        if forbidden_path.exists() or forbidden_path.is_symlink():
            return False, None
    try:
        expected = expected_sidecar_core(
            module,
            source_hash,
            checker_path,
            checker_hash,
            extra_paths,
            dependency_records,
            source_dir,
            artifact_mode,
        )
    except replay.ReplayPlanError:
        return False, None
    return core == expected, document if core == expected else None


def remove_module_paths(source_dir: Path, module: str, suffixes: Iterable[str]) -> None:
    for suffix in suffixes:
        path = source_dir / f"{module}{suffix}"
        try:
            metadata = path.lstat()
        except FileNotFoundError:
            continue
        if not stat.S_ISREG(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode):
            fail(f"refusing to remove non-regular stale output {path.name}")
        path.unlink()


def remove_compilation_receipts(source_dir: Path, manifest_stem: str) -> None:
    for artifact_mode in ARTIFACT_MODES:
        name = compilation_receipt_name(manifest_stem, artifact_mode)
        path = source_dir / name
        try:
            metadata = path.lstat()
        except FileNotFoundError:
            continue
        if not stat.S_ISREG(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode):
            fail(f"refusing to remove non-regular stale receipt {path.name}")
        path.unlink()


def remove_stale_module_outputs(
    source_dir: Path, module: str, artifact_mode: str
) -> None:
    suffixes = tuple(f".{kind}" for kind in artifact_kinds(artifact_mode))
    forbidden_suffixes = tuple(
        f".{kind}" for kind in forbidden_artifact_kinds(artifact_mode)
    )
    remove_module_paths(
        source_dir, module, suffixes + forbidden_suffixes + (".compiled.json",)
    )


def reject_forbidden_artifacts(
    source_dir: Path, module: str, artifact_mode: str
) -> None:
    for kind in forbidden_artifact_kinds(artifact_mode):
        path = source_dir / f"{module}.{kind}"
        if not path.exists() and not path.is_symlink():
            continue
        remove_stale_module_outputs(source_dir, module, artifact_mode)
        fail(
            f"checker emitted forbidden .{kind} artifact for {module} "
            f"in {artifact_mode} mode"
        )


def exclusive_write(
    path: Path, data: bytes, directory_identity: tuple[int, int]
) -> None:
    replay.exclusive_create_all(path.parent, directory_identity, {path: data})


def compile_plan(args: argparse.Namespace) -> None:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("compilation driver changed before execution")
    replay.validate_repository_location()
    source_dir, source_identity = scratch_directory(args.source_dir, "--source-dir")
    manifest_path = replay.project_path(args.manifest, "--manifest")
    manifest, manifest_bytes, sources = load_plan(
        manifest_path, source_dir, args.plan_sha256
    )
    graph = dependency_graph(sources)
    order = topological_order(graph)
    checker_path = replay.project_path(args.checker, "--checker")
    checker_bytes = read_regular_file(
        checker_path, "resource-bounded Lean checker", MAX_CHECKER_BYTES
    )
    checker_hash = sha256_bytes(checker_bytes)
    extra_dirs: list[Path] = []
    for index, raw in enumerate(args.extra_lean_path):
        directory, _identity = scratch_directory(raw, f"--extra-lean-path[{index}]")
        if directory == source_dir or directory in extra_dirs:
            fail("extra Lean paths must be distinct from the source directory")
        extra_dirs.append(directory)
    extra_paths = [replay.relative_project_path(path) for path in extra_dirs]
    if args.max_modules < 1 or args.timeout_seconds < 1:
        fail("module and timeout guards must be positive")
    artifact_mode = args.artifact_mode
    artifact_kinds(artifact_mode)

    compiled_records: dict[str, dict[str, object]] = {}
    reused = 0
    compiled = 0
    receipts_invalidated = False
    started = time.monotonic()
    for ordinal, module in enumerate(order):
        dependency_records = {
            dependency: compiled_records[dependency]["artifacts"]["olean"]
            for dependency in graph[module]
        }
        source_hash = sha256_bytes(sources[module])
        sidecar = sidecar_path(source_dir, module)
        valid, document = validate_sidecar(
            sidecar,
            module,
            source_hash,
            checker_path,
            checker_hash,
            extra_paths,
            dependency_records,
            source_dir,
            artifact_mode,
        )
        if valid and document is not None:
            compiled_records[module] = document
            reused += 1
            continue
        if compiled >= args.max_modules:
            break
        if not receipts_invalidated:
            remove_compilation_receipts(source_dir, manifest_path.stem)
            receipts_invalidated = True
        remove_stale_module_outputs(source_dir, module, artifact_mode)
        relative_source = (source_dir / f"{module}.lean").relative_to(REPOSITORY).as_posix()
        environment = os.environ.copy()
        environment["CK_EXTRA_LEAN_PATH"] = ":".join(str(path) for path in extra_dirs)
        environment["CK_ARTIFACT_MODE"] = artifact_mode
        module_started = time.monotonic()
        with (
            tempfile.TemporaryFile(
                mode="w+b", prefix=".lean-stdout-", dir=source_dir
            ) as stdout_file,
            tempfile.TemporaryFile(
                mode="w+b", prefix=".lean-stderr-", dir=source_dir
            ) as stderr_file,
        ):
            process = subprocess.Popen(
                ["/bin/zsh", str(checker_path), relative_source],
                cwd=REPOSITORY,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=stdout_file,
                stderr=stderr_file,
                start_new_session=True,
            )
            try:
                process.communicate(timeout=args.timeout_seconds)
            except subprocess.TimeoutExpired as error:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate()
                remove_stale_module_outputs(source_dir, module, artifact_mode)
                fail(f"Lean compilation timed out for {module}: {error}")
            try:
                stdout_size = file_size(stdout_file)
                stderr_size = file_size(stderr_file)
                if (
                    stdout_size > MAX_DIAGNOSTIC_BYTES
                    or stderr_size > MAX_DIAGNOSTIC_BYTES
                ):
                    fail(f"Lean diagnostics exceeded their guard for {module}")
                if process.returncode != 0:
                    diagnostic = (
                        read_file_tail(stdout_file, 8000)
                        + b"\n"
                        + read_file_tail(stderr_file, 8000)
                    ).decode("utf-8", errors="replace")[-8000:]
                    fail(f"Lean compilation failed for {module}: {diagnostic}")
                reject_forbidden_artifacts(source_dir, module, artifact_mode)
                core = expected_sidecar_core(
                    module,
                    source_hash,
                    checker_path,
                    checker_hash,
                    extra_paths,
                    dependency_records,
                    source_dir,
                    artifact_mode,
                )
                document = {
                    **core,
                    "sidecarPayloadSha256": sha256_bytes(canonical_json_bytes(core)),
                }
                exclusive_write(sidecar, pretty_json_bytes(document), source_identity)
            except replay.ReplayPlanError:
                remove_stale_module_outputs(source_dir, module, artifact_mode)
                raise
        compiled_records[module] = document
        compiled += 1
        print(
            json.dumps(
                {
                    "status": "compiled",
                    "artifactMode": artifact_mode,
                    "module": module,
                    "ordinal": ordinal,
                    "completedModules": reused + compiled,
                    "totalModules": len(order),
                    "seconds": round(time.monotonic() - module_started, 3),
                },
                sort_keys=True,
            ),
            flush=True,
        )

    if len(compiled_records) != len(order):
        print(
            json.dumps(
                {
                    "status": "partial",
                    "artifactMode": artifact_mode,
                    "compiledModules": compiled,
                    "reusedModules": reused,
                    "completedModules": len(compiled_records),
                    "remainingModules": len(order) - len(compiled_records),
                    "elapsedSeconds": round(time.monotonic() - started, 3),
                },
                sort_keys=True,
            ),
            flush=True,
        )
        return

    receipt_core: dict[str, object] = {
        "format": FORMAT,
        "compiler": {"file": SCRIPT.name, "byteSha256": SCRIPT_BYTE_SHA256},
        "artifactMode": artifact_mode,
        "planManifest": {
            "file": replay.relative_project_path(manifest_path),
            "byteSha256": sha256_bytes(manifest_bytes),
            "planSha256": manifest["planSha256"],
        },
        "checker": {
            "file": replay.relative_project_path(checker_path),
            "byteSha256": checker_hash,
        },
        "extraLeanPath": extra_paths,
        "moduleCount": len(order),
        "topologicalOrderSha256": sha256_bytes(canonical_json_bytes(order)),
        "modules": {
            module: {
                "sidecarPayloadSha256": compiled_records[module][
                    "sidecarPayloadSha256"
                ],
                **compiled_records[module]["artifacts"],
            }
            for module in order
        },
    }
    receipt = {
        **receipt_core,
        "receiptPayloadSha256": sha256_bytes(canonical_json_bytes(receipt_core)),
    }
    remove_compilation_receipts(source_dir, manifest_path.stem)
    receipt_name = compilation_receipt_name(manifest_path.stem, artifact_mode)
    receipt_path = source_dir / receipt_name
    rendered = pretty_json_bytes(receipt)
    exclusive_write(receipt_path, rendered, source_identity)
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("compilation driver changed during execution")
    if read_regular_file(
        checker_path, "resource-bounded Lean checker", MAX_CHECKER_BYTES
    ) != checker_bytes:
        fail("resource-bounded Lean checker changed during execution")
    print(
        json.dumps(
            {
                "status": "complete",
                "artifactMode": artifact_mode,
                "moduleCount": len(order),
                "receipt": receipt_name,
                "receiptPayloadSha256": receipt["receiptPayloadSha256"],
                "elapsedSeconds": round(time.monotonic() - started, 3),
            },
            sort_keys=True,
        ),
        flush=True,
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--source-dir", required=True)
    result.add_argument("--manifest", required=True)
    result.add_argument("--plan-sha256", required=True)
    result.add_argument("--checker", required=True)
    result.add_argument(
        "--artifact-mode",
        choices=ARTIFACT_MODES,
        default="pair",
        help="required output artifacts (default: pair = .olean plus .ilean)",
    )
    result.add_argument("--extra-lean-path", action="append", default=[])
    result.add_argument("--max-modules", type=int, default=20_000)
    result.add_argument("--timeout-seconds", type=int, default=1_800)
    return result


def main(argv: Iterable[str] | None = None) -> None:
    args = parser().parse_args(list(argv) if argv is not None else None)
    compile_plan(args)


if __name__ == "__main__":
    try:
        main()
    except replay.ReplayPlanError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
