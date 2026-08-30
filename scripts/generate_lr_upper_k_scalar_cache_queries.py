#!/usr/bin/env python3
"""Plan or emit exact scalar-cache queries for the patched upper-``K`` replay.

The direct replay repeatedly evaluates the same deterministic scalar
``A/C`` call at the same rational ``(s,y)`` point.  This tool authenticates
the same bridge receipt, patched streams, topology, and implementation as the
direct replay generator, reconstructs every leaf box with exact fractions,
and content-addresses those scalar calls.  Only calls whose multiplicity
reaches a caller-supplied threshold are selected.

``plan`` is read-only.  ``generate-queries`` emits bounded Lean modules whose
``#eval`` commands print dyadically rounded candidate values.  Those printed
values have no proof authority: a later ingestion stage must prove each
literal equal to the corresponding ``outerEnclosure`` by ordinary kernel
reduction and then use ``outerEnclosure_covers``.  Query emission uses
exclusive file creation inside a dedicated existing ``.lake/scratch`` child.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable, Iterator

import generate_lr_upper_k_historical_patched_replay as replay


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
FORMAT = "authenticated patched upper-K scalar-cache query plan v1"
CACHE_KEY_SCHEMA = "upper-k-scalar-cache-key-v1"
PROOF_AUTHORITY = (
    "none: query output is untrusted data; later ordinary Lean rfl' reductions "
    "and outerEnclosure_covers theorems are the sole authority"
)
CACHE_OVERLAY_SOURCE_FILES = (
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKCachedCornerValues.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKDirectCachedLeafCertificate.lean",
)
MAX_SELECTED_KEYS = 100_000
MAX_QUERY_MODULES = 20_000


@dataclass(frozen=True, slots=True)
class ExactBox:
    s_lo: Fraction
    s_hi: Fraction
    k_lo: Fraction
    k_hi: Fraction
    h_lo: Fraction
    h_hi: Fraction

    def center(self) -> "ExactBox":
        s = (self.s_lo + self.s_hi) / 2
        k = (self.k_lo + self.k_hi) / 2
        h = (self.h_lo + self.h_hi) / 2
        return ExactBox(s, s, k, k, h, h)

    def e_interval(self) -> tuple[Fraction, Fraction]:
        return self.s_lo * self.s_lo * self.k_lo, (
            self.s_hi * self.s_hi * self.k_hi
        )

    def y0_interval(self) -> tuple[Fraction, Fraction]:
        e_lo, e_hi = self.e_interval()
        return self.h_lo * self.h_lo * e_lo, self.h_hi * self.h_hi * e_hi


@dataclass(frozen=True, order=True, slots=True)
class ScalarKey:
    kind: str
    s: Fraction
    y: Fraction


@dataclass(frozen=True, slots=True)
class ScalarUse:
    field: str
    key: ScalarKey


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
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def fraction_record(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def exact_box_at(spec: replay.RootSpec, path: replay.PathSteps) -> ExactBox:
    box = ExactBox(
        spec.s_lo,
        spec.s_hi,
        spec.k_lo,
        spec.k_hi,
        spec.h_lo,
        spec.h_hi,
    )
    for step in path:
        if step.axis == "s":
            cut = (box.s_lo + box.s_hi) / 2
            box = (
                ExactBox(
                    box.s_lo,
                    cut,
                    box.k_lo,
                    box.k_hi,
                    box.h_lo,
                    box.h_hi,
                )
                if step.branch == 0
                else ExactBox(
                    cut,
                    box.s_hi,
                    box.k_lo,
                    box.k_hi,
                    box.h_lo,
                    box.h_hi,
                )
            )
        elif step.axis == "k":
            cut = (box.k_lo + box.k_hi) / 2
            box = (
                ExactBox(
                    box.s_lo,
                    box.s_hi,
                    box.k_lo,
                    cut,
                    box.h_lo,
                    box.h_hi,
                )
                if step.branch == 0
                else ExactBox(
                    box.s_lo,
                    box.s_hi,
                    cut,
                    box.k_hi,
                    box.h_lo,
                    box.h_hi,
                )
            )
        elif step.axis == "h":
            cut = (box.h_lo + box.h_hi) / 2
            box = (
                ExactBox(
                    box.s_lo,
                    box.s_hi,
                    box.k_lo,
                    box.k_hi,
                    box.h_lo,
                    cut,
                )
                if step.branch == 0
                else ExactBox(
                    box.s_lo,
                    box.s_hi,
                    box.k_lo,
                    box.k_hi,
                    cut,
                    box.h_hi,
                )
            )
        else:
            replay.fail(f"unexpected authenticated path axis {step.axis!r}")
    return box


def scalar_uses(box: ExactBox) -> tuple[ScalarUse, ...]:
    e_lo, e_hi = box.e_interval()
    y0_lo, y0_hi = box.y0_interval()
    return (
        ScalarUse("aY0Lower", ScalarKey("a", box.s_hi, y0_lo)),
        ScalarUse("aY0Upper", ScalarKey("a", box.s_lo, y0_hi)),
        ScalarUse("cY0Lower", ScalarKey("c", box.s_hi, y0_hi)),
        ScalarUse("cY0Upper", ScalarKey("c", box.s_lo, y0_lo)),
        ScalarUse("aELower", ScalarKey("a", box.s_hi, e_lo)),
        ScalarUse("aEUpper", ScalarKey("a", box.s_lo, e_hi)),
        ScalarUse("cELower", ScalarKey("c", box.s_hi, e_hi)),
        ScalarUse("cEUpper", ScalarKey("c", box.s_lo, e_lo)),
    )


def authenticated_leaves(
    authenticated: replay.AuthenticatedInputs,
) -> Iterator[tuple[str, replay.PathSteps, ExactBox]]:
    for spec in replay.ROOT_SPECS:
        root = authenticated.roots[spec.key]
        plan = replay.make_plan(root.tree, 1)
        if replay.reconstruct(plan) != root.topology:
            replay.fail(
                f"{spec.key} scalar-cache frontier does not reconstruct its stream"
            )
        for planned in replay.frontier(plan):
            if not planned.node.is_leaf or planned.node.token != "M":
                replay.fail(f"{spec.key} scalar-cache frontier contains a non-leaf")
            box = exact_box_at(spec, planned.path)
            independently_rendered = {
                "sLo": fraction_text(box.s_lo),
                "sHi": fraction_text(box.s_hi),
                "kLo": fraction_text(box.k_lo),
                "kHi": fraction_text(box.k_hi),
                "hLo": fraction_text(box.h_lo),
                "hHi": fraction_text(box.h_hi),
            }
            if independently_rendered != replay.bounds_at(spec, planned.path):
                replay.fail(
                    f"{spec.key} exact cache geometry disagrees at "
                    f"{replay.path_text(planned.path)}"
                )
            yield spec.key, planned.path, box


def cache_key_payload(key: ScalarKey, args: argparse.Namespace) -> dict[str, object]:
    return {
        "schema": CACHE_KEY_SCHEMA,
        "kind": key.kind,
        "s": fraction_record(key.s),
        "y": fraction_record(key.y),
        "dyadicBits": args.dyadic_bits,
        "terms": args.terms,
        "sqrtFuel": args.authenticated_sqrt_fuel,
        "logFuel": args.authenticated_log_fuel,
    }


def cache_id(key: ScalarKey, args: argparse.Namespace) -> str:
    return sha256_bytes(canonical_json_bytes(cache_key_payload(key, args)))


def bind_cache_overlay_sources() -> dict[str, object]:
    records: list[dict[str, object]] = []
    for relative in CACHE_OVERLAY_SOURCE_FILES:
        path = replay.project_path(relative, f"cache overlay source {relative}")
        data = replay.read_regular_file(
            path, f"cache overlay source {relative}", replay.MAX_INPUT_BYTES
        )
        records.append(
            {"file": relative, "bytes": len(data), "byteSha256": sha256_bytes(data)}
        )
    core: dict[str, object] = {
        "algorithm": replay.DIRECT_REPLAY_SOURCE_SET_ALGORITHM,
        "files": records,
    }
    return {**core, "sourceSetSha256": sha256_bytes(canonical_json_bytes(core))}


def query_module_prefix(raw: str) -> str:
    if re.fullmatch(r"Agent[A-Za-z0-9]+", raw) is None or len(raw) > 80:
        replay.fail("--module-prefix must be an ASCII Agent-prefixed Lean identifier")
    return raw


def chunks(values: list[Any], size: int) -> Iterator[list[Any]]:
    for index in range(0, len(values), size):
        yield values[index : index + size]


def render_query_module(
    prefix: str,
    index: int,
    entries: list[tuple[str, ScalarKey, int]],
    args: argparse.Namespace,
) -> tuple[str, str]:
    module = f"{prefix}Q{index:04d}"
    namespace = f"CourtadeKumar.{module}"
    lines = [
        "import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedCornerValues",
        "",
        "/-! Untrusted scalar-cache value queries; no theorem imports these results. -/",
        "",
        f"namespace {namespace}",
        "",
        "open LRUpperKDyadicOuterRounding",
        "",
    ]
    for entry_index, (identifier, key, _multiplicity) in enumerate(entries):
        name = f"query{entry_index:03d}"
        scalar = "aAutoI" if key.kind == "a" else "cAutoI"
        lines.extend(
            [
                f"def {name} : String × ℚ × ℚ :=",
                f"  let value := outerEnclosure {args.dyadic_bits}",
                f"    (LRUpperKHistoricalACValues.{scalar}",
                f"      {args.terms} {args.authenticated_sqrt_fuel}",
                f"      {args.authenticated_log_fuel} ({fraction_text(key.s)})",
                f"      ({fraction_text(key.y)}))",
                f"  ({json.dumps(identifier)}, value.lower, value.upper)",
                "",
                f"#eval {name}",
                "",
            ]
        )
    lines.extend([f"end {namespace}", ""])
    source = "\n".join(lines)
    if source.count("#eval ") != len(entries):
        replay.fail(f"{module} query count drifted during rendering")
    for forbidden in replay.FORBIDDEN_LEAN:
        if forbidden in source:
            replay.fail(f"{module} contains forbidden Lean token {forbidden!r}")
    return module, source


def build(
    args: argparse.Namespace, authenticated: replay.AuthenticatedInputs
) -> tuple[dict[str, str], dict[str, object]]:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        replay.fail("scalar-cache generator changed during planning")
    if sha256_bytes(replay.SCRIPT.read_bytes()) != replay.SCRIPT_BYTE_SHA256:
        replay.fail("direct replay generator changed during cache planning")

    args.authenticated_sqrt_fuel = authenticated.evaluator["parameters"]["sqrtFuel"]
    args.authenticated_log_fuel = authenticated.evaluator["parameters"]["logFuel"]
    direct_sources = replay.bind_direct_replay_sources()
    cache_sources = bind_cache_overlay_sources()
    counts: Counter[ScalarKey] = Counter()
    root_leaves: Counter[str] = Counter()
    leaf_count = 0
    for root_key, _path, box in authenticated_leaves(authenticated):
        leaf_count += 1
        root_leaves[root_key] += 1
        for domain in (box.center(), box):
            uses = scalar_uses(domain)
            if len(uses) != 8 or len({use.field for use in uses}) != 8:
                replay.fail("scalar-use field accounting drifted")
            counts.update(use.key for use in uses)

    expected_leaves = sum(root.stats.leaves for root in authenticated.roots.values())
    if leaf_count != expected_leaves:
        replay.fail("scalar-cache leaf count disagrees with authenticated streams")
    if sum(counts.values()) != 16 * leaf_count:
        replay.fail("scalar-cache occurrence count is not sixteen per leaf")
    if set(key.kind for key in counts) != {"a", "c"}:
        replay.fail("scalar-cache kind set drifted")

    selected = sorted(
        (
            (cache_id(key, args), key, multiplicity)
            for key, multiplicity in counts.items()
            if multiplicity >= args.cache_multiplicity_threshold
        ),
        key=lambda entry: entry[0],
    )
    if len(selected) > MAX_SELECTED_KEYS:
        replay.fail("selected scalar-cache keys exceed the hard guard")
    if len({identifier for identifier, _key, _count in selected}) != len(selected):
        replay.fail("content-address collision among selected scalar-cache keys")
    query_groups = list(chunks(selected, args.queries_per_module))
    if len(query_groups) > MAX_QUERY_MODULES:
        replay.fail("scalar-cache query modules exceed the hard guard")

    prefix = query_module_prefix(args.module_prefix)
    sources: dict[str, str] = {}
    query_records: list[dict[str, object]] = []
    selected_records: list[dict[str, object]] = []
    for index, group in enumerate(query_groups):
        module, source = render_query_module(prefix, index, group, args)
        if module in sources:
            replay.fail(f"duplicate scalar-cache query module {module}")
        sources[module] = source
        query_records.append(
            {
                "module": module,
                "firstCacheId": group[0][0],
                "lastCacheId": group[-1][0],
                "queryCount": len(group),
            }
        )
        for entry_index, (identifier, key, multiplicity) in enumerate(group):
            selected_records.append(
                {
                    "cacheId": identifier,
                    "kind": key.kind,
                    "s": fraction_record(key.s),
                    "y": fraction_record(key.y),
                    "multiplicity": multiplicity,
                    "queryModule": module,
                    "queryIndex": entry_index,
                }
            )

    output_hashes = {
        f"{module}.lean": sha256_bytes(source.encode("utf-8"))
        for module, source in sorted(sources.items())
    }
    served = sum(multiplicity for _identifier, _key, multiplicity in selected)
    receipt = authenticated.bridge_receipt
    manifest_core: dict[str, object] = {
        "format": FORMAT,
        "generator": {
            "file": SCRIPT.name,
            "byteSha256": SCRIPT_BYTE_SHA256,
            "directReplayGeneratorFile": replay.SCRIPT.name,
            "directReplayGeneratorByteSha256": replay.SCRIPT_BYTE_SHA256,
        },
        "proofAuthority": PROOF_AUTHORITY,
        "authenticatedInputs": {
            "bridgeReceiptFile": replay.relative_project_path(receipt.path),
            "bridgeReceiptByteSha256": sha256_bytes(receipt.file_bytes),
            "bridgeReceiptPayloadSha256": receipt.payload_sha256,
            "authoritativeProfileSha256": receipt.profile_sha256,
            "patchedManifestFile": replay.relative_project_path(
                authenticated.manifest_path
            ),
            "patchedManifestByteSha256": sha256_bytes(
                authenticated.manifest_bytes
            ),
            "patchedManifestPayloadSha256": authenticated.manifest[
                "resultPayloadSha256"
            ],
            "streamsAggregateSha256": authenticated.manifest[
                "streamsAggregateSha256"
            ],
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
            "cachedOverlay": cache_sources,
        },
        "parameters": {
            "cacheKeySchema": CACHE_KEY_SCHEMA,
            "dyadicBits": args.dyadic_bits,
            "terms": args.terms,
            "sqrtFuel": args.authenticated_sqrt_fuel,
            "logFuel": args.authenticated_log_fuel,
            "cacheMultiplicityThreshold": args.cache_multiplicity_threshold,
            "queriesPerModule": args.queries_per_module,
            "modulePrefix": prefix,
        },
        "outputDirectory": replay.relative_project_path(args.validated_output_dir),
        "rootLeaves": dict(sorted(root_leaves.items())),
        "totalLeaves": leaf_count,
        "totalScalarOccurrences": sum(counts.values()),
        "uniqueScalarKeys": len(counts),
        "selectedScalarKeys": len(selected),
        "selectedScalarOccurrences": served,
        "eliminatedDuplicateMaterializations": served - len(selected),
        "unselectedScalarOccurrences": sum(counts.values()) - served,
        "resultingScalarMaterializations": (
            sum(counts.values()) - served + len(selected)
        ),
        "queryModuleCount": len(sources),
        "queries": query_records,
        "selected": selected_records,
        "outputs": output_hashes,
    }
    plan_sha = sha256_bytes(canonical_json_bytes(manifest_core))
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        replay.fail("scalar-cache generator changed while rendering")
    if sha256_bytes(replay.SCRIPT.read_bytes()) != replay.SCRIPT_BYTE_SHA256:
        replay.fail("direct replay generator changed while rendering cache plan")
    if replay.bind_direct_replay_sources() != direct_sources:
        replay.fail("direct replay implementation changed while cache plan rendered")
    if bind_cache_overlay_sources() != cache_sources:
        replay.fail("cached overlay implementation changed while cache plan rendered")
    return sources, {**manifest_core, "planSha256": plan_sha}


def summary(manifest: dict[str, object]) -> dict[str, object]:
    return {
        "status": "validated-read-only",
        "planSha256": manifest["planSha256"],
        "bridgeReceiptPayloadSha256": manifest["authenticatedInputs"][
            "bridgeReceiptPayloadSha256"
        ],
        "outputDirectory": manifest["outputDirectory"],
        "totalLeaves": manifest["totalLeaves"],
        "totalScalarOccurrences": manifest["totalScalarOccurrences"],
        "uniqueScalarKeys": manifest["uniqueScalarKeys"],
        "selectedScalarKeys": manifest["selectedScalarKeys"],
        "selectedScalarOccurrences": manifest["selectedScalarOccurrences"],
        "eliminatedDuplicateMaterializations": manifest[
            "eliminatedDuplicateMaterializations"
        ],
        "resultingScalarMaterializations": manifest[
            "resultingScalarMaterializations"
        ],
        "queryModuleCount": manifest["queryModuleCount"],
    }


def validate_arguments(args: argparse.Namespace) -> None:
    replay.validate_positive_arguments(args)
    if not 2 <= args.cache_multiplicity_threshold <= 1_000_000:
        replay.fail("--cache-multiplicity-threshold must lie in [2,1000000]")
    if not 1 <= args.queries_per_module <= 64:
        replay.fail("--queries-per-module must lie in [1,64]")
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
        replay.fail("refusing query emission without --confirm-write")
    sources, manifest = prepared(args)
    expected = replay.supplied_hex64(
        args.expected_plan_sha256, "--expected-plan-sha256"
    )
    if expected != manifest["planSha256"]:
        replay.fail("--expected-plan-sha256 differs from the fresh cache plan")
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
        replay.fail(f"refusing to overwrite scalar-cache outputs: {sorted(collisions)}")
    replay.exclusive_create_all(
        directory, args.validated_output_identity, outputs
    )
    written = summary(manifest)
    written.update(
        {"status": "written", "writtenFiles": len(outputs), "manifest": manifest_name}
    )
    print(json.dumps(written, sort_keys=True))


def add_arguments(command: argparse.ArgumentParser) -> None:
    replay.add_common_arguments(command)
    command.add_argument("--cache-multiplicity-threshold", type=int, default=4)
    command.add_argument("--queries-per-module", type=int, default=32)
    command.set_defaults(module_prefix="AgentUpperKScalarCacheQueryGenerated")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="authenticate and plan without writing")
    add_arguments(plan)
    plan.set_defaults(handler=command_plan)
    generate = commands.add_parser(
        "generate-queries", help="emit bounded untrusted Lean query modules"
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
