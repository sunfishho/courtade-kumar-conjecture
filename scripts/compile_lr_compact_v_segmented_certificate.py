#!/usr/bin/env python3
"""Sequential, resumable compiler for segmented compact-V replay modules."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path


class CompileError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise CompileError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".building")
    encoded = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    with temporary.open("wb") as handle:
        handle.write(encoded)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def dependency_digest(paths: list[Path]) -> str:
    digest = hashlib.sha256()
    for path in paths:
        if not path.is_file():
            fail(f"missing dependency artifact {path}")
        digest.update(str(path).encode())
        digest.update(b"\0")
        digest.update(sha256(path).encode())
        digest.update(b"\0")
    return digest.hexdigest()


def load_json(path: Path) -> dict:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"cannot read {path}: {error}")
    if not isinstance(value, dict):
        fail(f"{path} is not a JSON object")
    return value


def validate_sources(generated_dir: Path, manifest: dict) -> list[str]:
    required = {"format", "terminalCount", "files", "modulePrefix"}
    if not required <= set(manifest):
        fail("generated manifest is missing required fields")
    if manifest["format"] != "compact-v-segmented-replay-v1":
        fail("unsupported generated manifest format")
    count = manifest["terminalCount"]
    if not isinstance(count, int) or count <= 0:
        fail("invalid terminal count")
    names = ["Config.lean"] + [f"Leaf{index:03d}.lean" for index in range(count)]
    names.append("Assembly.lean")
    recorded = manifest["files"]
    if not isinstance(recorded, dict) or set(recorded) != set(names):
        fail("manifest source inventory does not match expected modules")
    forbidden = ("native_decide", "vm_decide", "ofReduceBool", "trustCompiler",
                 "run_tac", "sorry", "admit")
    for name in names:
        source = generated_dir / name
        if not source.is_file() or sha256(source) != recorded[name]:
            fail(f"source hash mismatch for {source}")
        text = source.read_text()
        hit = next((token for token in forbidden if token in text), None)
        if hit is not None:
            fail(f"forbidden token {hit!r} in {source}")
        expected_checks = 1 if name.startswith("Leaf") else 0
        if text.count("#kernel_checked_bool") != expected_checks:
            fail(f"wrong arithmetic declaration count in {source}")
    return names


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("generated_dir", type=Path)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--state", type=Path)
    args = parser.parse_args()
    try:
        project = args.project_root.resolve()
        generated = (project / args.generated_dir).resolve()
        manifest = load_json(generated / "manifest.json")
        names = validate_sources(generated, manifest)
        module_prefix = manifest["modulePrefix"]
        if not isinstance(module_prefix, str):
            fail("manifest modulePrefix is not a string")
        expected_suffix = Path(*module_prefix.split("."))
        try:
            relative_generated = generated.relative_to(project)
        except ValueError:
            fail("generated directory lies outside the project")
        if relative_generated != expected_suffix:
            fail("generated directory does not match manifest modulePrefix")
        lean_path = os.environ.get("LEAN_PATH")
        if not lean_path:
            fail("LEAN_PATH must be supplied explicitly")
        if not args.lean.is_file():
            fail(f"Lean executable does not exist: {args.lean}")
        version = subprocess.run(
            [str(args.lean), "--version"], check=True,
            text=True, capture_output=True).stdout.strip()
        command_identity = hashlib.sha256(json.dumps({
            "lean": str(args.lean.resolve()),
            "version": version,
            "leanPath": lean_path,
            "options": ["-j1", "-t0", "-M6000", "-s65520",
                        "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"],
        }, sort_keys=True).encode()).hexdigest()
        build_root = project / ".lake/build/lib/lean"
        output_dir = build_root / expected_suffix
        output_dir.mkdir(parents=True, exist_ok=True)
        state_path = args.state or (
            project / ".lake/scratch" /
            (module_prefix.split(".")[-1] + "-compile-state.json"))
        if state_path.exists():
            state = load_json(state_path)
        else:
            state = {"format": "compact-v-segmented-compile-state-v1",
                     "modules": {}}
        if state.get("format") != "compact-v-segmented-compile-state-v1":
            fail("unsupported compile-state format")
        records = state.setdefault("modules", {})
        if not isinstance(records, dict):
            fail("compile-state modules field is invalid")
        common = [
            build_root / "InformationTheory/CourtadeKumar/LRCompactVStagedGroupedCheckedTree.olean",
            build_root / "InformationTheory/CourtadeKumar/KernelCheckedBoolCommand.olean",
        ]
        config_output = output_dir / "Config.olean"
        leaf_outputs = [output_dir / f"Leaf{index:03d}.olean"
                        for index in range(manifest["terminalCount"])]
        started = time.monotonic()
        compiled = 0
        skipped = 0
        for ordinal, name in enumerate(names, start=1):
            stem = name.removesuffix(".lean")
            source = generated / name
            output = output_dir / f"{stem}.olean"
            if name == "Config.lean":
                dependencies = common
            elif name.startswith("Leaf"):
                dependencies = common + [config_output]
            else:
                dependencies = common + [config_output] + leaf_outputs
            source_hash = sha256(source)
            deps_hash = dependency_digest(dependencies)
            record = records.get(name)
            if (isinstance(record, dict)
                    and record.get("sourceSha256") == source_hash
                    and record.get("dependencySha256") == deps_hash
                    and record.get("commandIdentity") == command_identity
                    and output.is_file()
                    and record.get("oleanSha256") == sha256(output)):
                skipped += 1
                print(f"[{ordinal}/{len(names)}] skip {stem}", flush=True)
                continue
            temporary = output.with_name(output.name + ".building")
            if temporary.exists():
                temporary.unlink()
            command = [
                str(args.lean), "-j1", "-t0", "-M6000", "-s65520",
                "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                "-o", str(temporary), str(source),
            ]
            print(f"[{ordinal}/{len(names)}] compile {stem}", flush=True)
            module_started = time.monotonic()
            result = subprocess.run(command, cwd=project)
            if result.returncode != 0:
                if temporary.exists():
                    temporary.unlink()
                fail(f"Lean failed for {source} with exit code {result.returncode}")
            if not temporary.is_file() or temporary.stat().st_size == 0:
                fail(f"Lean produced no artifact for {source}")
            os.replace(temporary, output)
            records[name] = {
                "sourceSha256": source_hash,
                "dependencySha256": deps_hash,
                "commandIdentity": command_identity,
                "oleanSha256": sha256(output),
                "elapsedSeconds": round(time.monotonic() - module_started, 3),
            }
            state["modulePrefix"] = module_prefix
            state["planSha256"] = manifest["planSha256"]
            atomic_json(state_path, state)
            compiled += 1
            print(f"  done in {records[name]['elapsedSeconds']:.3f}s", flush=True)
        print(json.dumps({
            "compiled": compiled,
            "skipped": skipped,
            "modules": len(names),
            "elapsedSeconds": round(time.monotonic() - started, 3),
            "state": str(state_path),
        }, sort_keys=True), flush=True)
    except (CompileError, OSError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
