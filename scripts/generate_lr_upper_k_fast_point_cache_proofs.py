#!/usr/bin/env python3
"""Plan or emit kernel-authenticated upper-``K`` fast point modules.

This stage authenticates the fast point query plan, the complete serial
collection receipt, every collected output byte, and the exact Lean APIs used
by the generated proof.  It then emits one ``CertifiedPoint`` definition per
materialized rational point.  Each entry contains a complete literal
``LRQPointCertificate``, the two shared rounded logarithm enclosures, and
literal rounded ``Q`` and ``Q'`` enclosures.  The data, two records of
independent arithmetic checks, semantic soundness theorem, and final
``CertifiedPoint`` are separate Lean declarations.  Ordinary ``rfl'``
reductions check the square-root facts and identify the four outward-rounded
enclosures.  Four stack-safe, kernel-checked ``norm_num`` proofs verify the
logarithm range-reduction facts through shallow endpoint identities.  The proved
``outerEnclosure_covers`` theorem transports the four isolated equalities to
semantic containment.  Six atomic Boolean facts replace the one stack-hungry
monolithic point-check reduction.  This deliberately avoids both a deeply
nested proof term and negative-power rational normalization through raw
definitional reduction.  No generated
proof reruns automatic logarithm normalization or the polynomial square-root
construction, and each logarithm series is evaluated only once.

The query output and this Python program have no proof authority.  The
generated reductions and imported Lean theorems are checked by the ordinary
Lean kernel.  Modules preserve authenticated first-use order, allowing later
leaf generators to import only the nearby point modules they actually need.
Emission is exclusive and confined to a dedicated existing repository-local
``.lake/scratch`` child directory.
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

import collect_lr_upper_k_fast_point_cache_queries as collection
import generate_lr_upper_k_fast_point_cache_values as pure_values


sys.dont_write_bytecode = True

SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
FORMAT = "kernel-authenticated upper-K fast point-cache proof plan v4"
PROOF_AUTHORITY = (
    "two isolated ordinary Lean rfl' reductions and four isolated "
    "kernel-checked norm_num proofs for each literal point certificate; "
    "one isolated equality reduction for each of its two cached logarithm "
    "enclosures and each of its two literal Q/Q' enclosures; followed only "
    "by proved atomic-check assembly, outerEnclosure_covers, and cached-log "
    "point soundness"
)
MAX_RECEIPT_BYTES = 32 * 1024 * 1024
MAX_GENERATED_MODULES = 20_000
MAX_GENERATED_SOURCE_BYTES = 512 * 1024 * 1024
MAX_MANIFEST_BYTES = 512 * 1024 * 1024
GENERATED_NAMESPACE = "LRUpperKFastPointCacheProofGenerated"
AUTHENTICATED_POINT_LOWER = Fraction(148137, 549755813888)
AUTHENTICATED_POINT_UPPER = Fraction(287, 8192)
POINT_PROOF_SOURCE_FILES = (
    "InformationTheory/CourtadeKumar/"
    "ExactLogEnclosure.lean",
    "InformationTheory/CourtadeKumar/"
    "ExactSqrtEnclosure.lean",
    "InformationTheory/CourtadeKumar/"
    "LRCertificateQEnclosure.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKEnclosureCovers.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKDyadicOuterRoundingCore.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKPointSoundCore.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKCachedLogPointCore.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKCachedLogPointCertificate.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantQPointCertificateAtomicCheck.lean",
    "InformationTheory/CourtadeKumar/"
    "LRDeterminantUpperKLiteralCachedLogPointCertificate.lean",
)


@dataclass(frozen=True, slots=True)
class CacheEntry:
    cache_id: str
    z: Fraction
    leaf_multiplicity: int
    first_use_ordinal: int
    query_module: str
    query_index: int
    value: collection.ParsedValue


def fail(message: str) -> None:
    raise collection.query_plan.replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return collection.canonical_json_bytes(value)


def canonical_json_sha256(value: object) -> str:
    """Hash the proof manifest while streaming its large entry array."""
    if not isinstance(value, dict) or not isinstance(value.get("entries"), list):
        return sha256_bytes(canonical_json_bytes(value))
    hasher = hashlib.sha256()
    hasher.update(b"{")
    first_field = True
    for key in sorted(value):
        if not first_field:
            hasher.update(b",")
        hasher.update(canonical_json_bytes(key))
        hasher.update(b":")
        field = value[key]
        if key == "entries":
            hasher.update(b"[")
            # Encoding small batches is much faster than ``iterencode`` while
            # bounding the temporary canonical JSON to roughly one megabyte.
            # Strip each batch's brackets and insert exactly the comma that a
            # single canonical array would contain between adjacent batches.
            for start in range(0, len(field), 1024):
                if start:
                    hasher.update(b",")
                batch = canonical_json_bytes(field[start : start + 1024])
                hasher.update(memoryview(batch)[1:-1])
            hasher.update(b"]")
        else:
            hasher.update(canonical_json_bytes(field))
        first_field = False
    hasher.update(b"}")
    return hasher.hexdigest()


def canonical_record_array_sha256(values: Iterable[collection.ParsedValue]) -> str:
    """Hash records without allocating a second full in-memory JSON tree."""
    hasher = hashlib.sha256()
    hasher.update(b"[")
    first = True
    for value in values:
        if not first:
            hasher.update(b",")
        hasher.update(canonical_json_bytes(value.record()))
        first = False
    hasher.update(b"]")
    return hasher.hexdigest()


def pretty_json_bytes(value: object) -> bytes:
    data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if len(data) > MAX_MANIFEST_BYTES:
        fail("fast point-cache proof manifest exceeds its hard byte guard")
    return data


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


def typed_fraction_text(value: Fraction) -> str:
    return f"({fraction_text(value)} : ℚ)"


def proof_module_prefix(raw: str) -> str:
    if re.fullmatch(r"Agent[A-Za-z0-9]+", raw) is None or len(raw) > 80:
        fail("--module-prefix must be an ASCII Agent-prefixed Lean identifier")
    return raw


def chunks(values: list[Any], size: int) -> Iterator[list[Any]]:
    for index in range(0, len(values), size):
        yield values[index : index + size]


def bind_point_proof_sources() -> dict[str, object]:
    records: list[dict[str, object]] = []
    for relative in POINT_PROOF_SOURCE_FILES:
        path = collection.query_plan.replay.project_path(
            relative, f"fast point proof source {relative}"
        )
        data = collection.query_plan.replay.read_regular_file(
            path,
            f"fast point proof source {relative}",
            collection.query_plan.replay.MAX_INPUT_BYTES,
        )
        records.append(
            {"file": relative, "bytes": len(data), "byteSha256": sha256_bytes(data)}
        )
    core: dict[str, object] = {
        "algorithm": collection.query_plan.replay.DIRECT_REPLAY_SOURCE_SET_ALGORITHM,
        "files": records,
    }
    return {**core, "sourceSetSha256": sha256_bytes(canonical_json_bytes(core))}


def validate_optional_evaluator(
    receipt: dict[str, Any], parameters: dict[str, Any]
) -> dict[str, object] | None:
    record = receipt.get("evaluator")
    if record is None:
        return None
    if sha256_bytes(pure_values.SCRIPT.read_bytes()) != pure_values.SCRIPT_BYTE_SHA256:
        fail("pure fast point value driver changed while its receipt was validated")
    if (
        sha256_bytes(pure_values.evaluator.SCRIPT.read_bytes())
        != pure_values.evaluator.SCRIPT_BYTE_SHA256
    ):
        fail("exact Fraction point evaluator changed while its receipt was validated")
    expected = pure_values.evaluator_record(parameters)
    if record != expected:
        fail("fast point-cache receipt has a stale or malformed evaluator binding")
    return expected


def load_query_manifest(
    query_dir: Path, manifest_path: Path
) -> tuple[dict[str, Any], list[tuple[str, Path, Any]], bytes]:
    if manifest_path.parent != query_dir:
        fail("--query-manifest must be directly inside --query-dir")
    data = read_regular_file(
        manifest_path,
        "fast point-cache query manifest",
        collection.query_plan.MAX_MANIFEST_BYTES,
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
    modules: list[tuple[str, Path, Any]],
) -> tuple[dict[str, Any], dict[str, collection.ParsedValue], bytes]:
    if receipt_path.parent != collection_dir:
        fail("--collection-receipt must be directly inside --collection-dir")
    data = read_regular_file(
        receipt_path, "fast point-cache collection receipt", MAX_RECEIPT_BYTES
    )
    try:
        receipt = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse fast point-cache collection receipt: {error}")
    if not isinstance(receipt, dict):
        fail("fast point-cache collection receipt must be a JSON object")
    payload_sha = receipt.get("receiptPayloadSha256")
    if (
        not isinstance(payload_sha, str)
        or re.fullmatch(r"[0-9a-f]{64}", payload_sha) is None
    ):
        fail("fast point-cache collection receipt payload hash is invalid")
    core = dict(receipt)
    del core["receiptPayloadSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != payload_sha:
        fail("fast point-cache receipt payload hash does not authenticate its content")
    if receipt.get("format") != collection.RECEIPT_FORMAT:
        fail("fast point-cache collection receipt format drifted")
    if receipt.get("proofAuthority") != (
        "none: collected values remain untrusted until ordinary Lean kernel "
        "reductions authenticate them"
    ):
        fail("fast point-cache collection proof-authority declaration drifted")
    if receipt.get("certificateScheme") != query_manifest["parameters"][
        "certificateScheme"
    ]:
        fail("fast point-cache collection certificate scheme drifted")
    if receipt.get("resultSetHashAlgorithm") != collection.RESULT_SET_HASH_ALGORITHM:
        fail("fast point-cache collection result-set hash algorithm drifted")
    validate_optional_evaluator(receipt, query_manifest["parameters"])
    expected_collector = {
        "file": collection.SCRIPT.name,
        "byteSha256": collection.SCRIPT_BYTE_SHA256,
    }
    if receipt.get("collector") != expected_collector:
        fail("collection receipt is not bound to the current fast point collector")
    checker_bytes = read_regular_file(
        collection.CHECKER, "repository-local Lean checker", 64_000
    )
    if receipt.get("checker") != {
        "file": collection.CHECKER.name,
        "byteSha256": sha256_bytes(checker_bytes),
    }:
        fail("fast point-cache receipt checker binding drifted")
    expected_query_record = {
        "file": collection.query_plan.replay.relative_project_path(
            query_manifest_path
        ),
        "byteSha256": sha256_bytes(query_manifest_bytes),
        "planSha256": query_manifest["planSha256"],
    }
    if receipt.get("queryManifest") != expected_query_record:
        fail("fast point-cache receipt query-manifest binding drifted")
    if receipt.get("moduleCount") != len(modules) or receipt.get(
        "valueCount"
    ) != query_manifest["selectedPointKeys"]:
        fail("fast point-cache receipt counts disagree with the query plan")
    outputs = receipt.get("outputs")
    if not isinstance(outputs, dict) or len(outputs) != len(modules):
        fail("fast point-cache receipt output table is malformed")

    values: list[collection.ParsedValue] = []
    expected_output_names: set[str] = set()
    parameters = query_manifest["parameters"]
    for module, _source, expected_records in modules:
        filename = f"{module}.out"
        expected_output_names.add(filename)
        record = outputs.get(filename)
        if not isinstance(record, dict) or set(record) != {
            "bytes",
            "byteSha256",
            "queryCount",
        }:
            fail(f"fast point-cache receipt lacks a strict record for {filename}")
        path = collection_dir / filename
        output_bytes = read_regular_file(
            path,
            f"collected fast point-cache output {filename}",
            collection.MAX_STDOUT_BYTES,
        )
        if record != {
            "bytes": len(output_bytes),
            "byteSha256": sha256_bytes(output_bytes),
            "queryCount": len(expected_records),
        }:
            fail(f"fast point-cache receipt output record drifted for {filename}")
        values.extend(
            collection.parse_output(output_bytes, expected_records, parameters)
        )
    if set(outputs) != expected_output_names:
        fail("fast point-cache receipt contains unexpected output records")
    if canonical_record_array_sha256(values) != receipt.get("resultSetSha256"):
        fail("fast point-cache collection result-set hash drifted")
    by_id = {value.cache_id: value for value in values}
    if len(by_id) != len(values):
        fail("fast point-cache collection repeats a cache ID")
    return receipt, by_id, data


def exact_entries(
    query_manifest: dict[str, Any], values: dict[str, collection.ParsedValue]
) -> list[CacheEntry]:
    selected = query_manifest.get("selected")
    if not isinstance(selected, list):
        fail("fast point-cache query manifest selected table is malformed")
    parameters = query_manifest.get("parameters")
    if not isinstance(parameters, dict):
        fail("fast point-cache query manifest parameters are malformed")
    if parameters.get("certificateScheme") != collection.query_plan.FAST_CERTIFICATE_SCHEME:
        fail("fast point-cache certificate scheme drifted")
    key_args = argparse.Namespace(
        dyadic_bits=parameters["pointDyadicBits"],
        point_sqrt_bits=parameters["sqrtDyadicBits"],
        terms=parameters["terms"],
        authenticated_log_fuel=parameters["logFuel"],
    )
    threshold = parameters["cacheMultiplicityThreshold"]
    result: list[CacheEntry] = []
    previous_first_use = -1
    for index, record in enumerate(selected):
        if not isinstance(record, dict):
            fail(f"selected[{index}] is not an object")
        identifier = record.get("cacheId")
        multiplicity = record.get("leafMultiplicity")
        first_use = record.get("firstUseOrdinal")
        query_module = record.get("queryModule")
        query_index = record.get("queryIndex")
        if (
            not isinstance(identifier, str)
            or re.fullmatch(r"[0-9a-f]{64}", identifier) is None
            or identifier not in values
            or not isinstance(multiplicity, int)
            or isinstance(multiplicity, bool)
            or multiplicity < threshold
            or not isinstance(first_use, int)
            or isinstance(first_use, bool)
            or first_use <= previous_first_use
            or not isinstance(query_module, str)
            or not isinstance(query_index, int)
            or isinstance(query_index, bool)
            or query_index < 0
        ):
            fail(f"selected[{index}] has invalid proof or locality metadata")
        z = fraction_from_record(record.get("z"), f"selected[{index}].z")
        if not AUTHENTICATED_POINT_LOWER <= z <= AUTHENTICATED_POINT_UPPER:
            fail(f"selected[{index}] escaped the authenticated point range")
        if collection.query_plan.cache_id(z, key_args) != identifier:
            fail(f"selected[{index}] cache ID does not hash its exact point key")
        value = values[identifier]
        if value.z != z:
            fail(f"selected[{index}] collected point differs from its exact key")
        result.append(
            CacheEntry(
                identifier,
                z,
                multiplicity,
                first_use,
                query_module,
                query_index,
                value,
            )
        )
        previous_first_use = first_use
    if len(result) != query_manifest.get("selectedPointKeys"):
        fail("fast point-cache selected count drifted")
    if {entry.cache_id for entry in result} != set(values):
        fail("fast point-cache query plan and collection have different ID sets")
    return result


def render_config(
    prefix: str,
    parameters: dict[str, Any],
    query_manifest: dict[str, Any],
    receipt: dict[str, Any],
    query_implementation: dict[str, object],
    proof_implementation: dict[str, object],
) -> tuple[str, str]:
    module = f"{prefix}Config"
    source = f"""import InformationTheory.CourtadeKumar.LRDeterminantUpperKLiteralCachedLogPointCertificate

/-! Authenticated constants for the generated upper-`K` fast point cache. -/

namespace CourtadeKumar.{GENERATED_NAMESPACE}

def pointDyadicBits : ℕ := {parameters["pointDyadicBits"]}
def logDyadicBits : ℕ := {parameters["logDyadicBits"]}
def terms : ℕ := {parameters["terms"]}
def sqrtDyadicBits : ℕ := {parameters["sqrtDyadicBits"]}
def logFuel : ℕ := {parameters["logFuel"]}

def queryPlanSha256 : String := {json.dumps(query_manifest["planSha256"])}
def collectionResultSetSha256 : String :=
  {json.dumps(receipt["resultSetSha256"])}
def collectionReceiptPayloadSha256 : String :=
  {json.dumps(receipt["receiptPayloadSha256"])}
def queryFastPointSourceSetSha256 : String :=
  {json.dumps(query_implementation["fastPointCache"]["sourceSetSha256"])}
def pointProofSourceSetSha256 : String :=
  {json.dumps(proof_implementation["sourceSetSha256"])}

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
) -> tuple[str, bytes, list[dict[str, object]]]:
    module = f"{prefix}P{index:04d}"
    namespace = f"P{index:04d}"
    lines = [
        f"import {config_module}",
        "",
        "/-! Kernel-authenticated rounded Q/Q' point entries. -/",
        "",
        f"namespace CourtadeKumar.{GENERATED_NAMESPACE}",
        f"namespace {namespace}",
        "",
        "open Set",
        "",
        f"set_option maxRecDepth {max_rec_depth}",
        f"set_option maxHeartbeats {max_heartbeats}",
        "",
    ]
    records: list[dict[str, object]] = []
    for entry in entries:
        tag = entry.cache_id[:16]
        point_name = f"point_{tag}"
        certificate_name = f"certificate_{tag}"
        logs_name = f"logs_{tag}"
        values_name = f"values_{tag}"
        checks_name = f"atomicChecks_{tag}"
        outer_equalities_name = f"outerEqualities_{tag}"
        sound_name = f"sound_{tag}"
        z = typed_fraction_text(entry.z)
        sqrt_lower = typed_fraction_text(entry.value.sqrt_lower)
        sqrt_upper = typed_fraction_text(entry.value.sqrt_upper)
        log_lower_lower_exponent = (
            f"({entry.value.log_lower_lower_exponent} : ℤ)"
        )
        log_lower_lower_mantissa = typed_fraction_text(
            entry.value.log_lower_lower_mantissa
        )
        log_lower_upper_exponent = (
            f"({entry.value.log_lower_upper_exponent} : ℤ)"
        )
        log_lower_upper_mantissa = typed_fraction_text(
            entry.value.log_lower_upper_mantissa
        )
        log_upper_lower_exponent = (
            f"({entry.value.log_upper_lower_exponent} : ℤ)"
        )
        log_upper_lower_mantissa = typed_fraction_text(
            entry.value.log_upper_lower_mantissa
        )
        log_upper_upper_exponent = (
            f"({entry.value.log_upper_upper_exponent} : ℤ)"
        )
        log_upper_upper_mantissa = typed_fraction_text(
            entry.value.log_upper_upper_mantissa
        )
        log_lower_enclosure_lower = typed_fraction_text(
            entry.value.log_lower_enclosure_lower
        )
        log_lower_enclosure_upper = typed_fraction_text(
            entry.value.log_lower_enclosure_upper
        )
        log_upper_enclosure_lower = typed_fraction_text(
            entry.value.log_upper_enclosure_lower
        )
        log_upper_enclosure_upper = typed_fraction_text(
            entry.value.log_upper_enclosure_upper
        )
        q_lower = typed_fraction_text(entry.value.q_lower)
        q_upper = typed_fraction_text(entry.value.q_upper)
        q_prime_lower = typed_fraction_text(entry.value.q_prime_lower)
        q_prime_upper = typed_fraction_text(entry.value.q_prime_upper)
        lines.extend(
            [
                f"def {certificate_name} : LRQPointCertificate :=",
                "  { sqrtOneSub :=",
                f"        {{ lower := {sqrt_lower}",
                f"          upper := {sqrt_upper} }}",
                "    logLowerProbability :=",
                "        { lower :=",
                f"            {{ exponent := {log_lower_lower_exponent}",
                f"              mantissa := {log_lower_lower_mantissa} }}",
                "          upper :=",
                f"            {{ exponent := {log_lower_upper_exponent}",
                f"              mantissa := {log_lower_upper_mantissa} }} }}",
                "    logUpperProbability :=",
                "        { lower :=",
                f"            {{ exponent := {log_upper_lower_exponent}",
                f"              mantissa := {log_upper_lower_mantissa} }}",
                "          upper :=",
                f"            {{ exponent := {log_upper_upper_exponent}",
                f"              mantissa := {log_upper_upper_mantissa} }} }} }}",
                "",
                f"def {logs_name} :",
                "    LRUpperKCachedLogPointCertificate.LogValues :=",
                "  { lower :=",
                f"        {{ lower := {log_lower_enclosure_lower}",
                f"          upper := {log_lower_enclosure_upper} }}",
                "    upper :=",
                f"        {{ lower := {log_upper_enclosure_lower}",
                f"          upper := {log_upper_enclosure_upper} }} }}",
                "",
                f"def {values_name} : LRUpperKPointCache.Values :=",
                "  { q :=",
                f"        {{ lower := {q_lower}",
                f"          upper := {q_upper} }}",
                "    qPrime :=",
                f"        {{ lower := {q_prime_lower}",
                f"          upper := {q_prime_upper} }} }}",
                "",
                f"theorem {checks_name} :",
                "    LRQPointCertificate.AtomicChecks",
                f"      {z} {certificate_name} :=",
                "  { sqrt := by rfl'",
                "    lowerLower := by",
                "      norm_num [RationalEnclosure.LogRangeCertificate.check,",
                f"        {certificate_name},",
                "        LRQPointCertificate.lowerProbability_lower_eq]",
                "    lowerUpper := by",
                "      norm_num [RationalEnclosure.LogRangeCertificate.check,",
                f"        {certificate_name},",
                "        LRQPointCertificate.lowerProbability_upper_eq]",
                "    upperLower := by",
                "      norm_num [RationalEnclosure.LogRangeCertificate.check,",
                f"        {certificate_name},",
                "        LRQPointCertificate.upperProbability_lower_eq]",
                "    upperUpper := by",
                "      norm_num [RationalEnclosure.LogRangeCertificate.check,",
                f"        {certificate_name},",
                "        LRQPointCertificate.upperProbability_upper_eq]",
                "    sqrtPositive := by rfl' }",
                "",
                f"theorem {outer_equalities_name} :",
                "    LRUpperKLiteralCachedLogPointCertificate.OuterEqualities",
                "      pointDyadicBits logDyadicBits terms",
                f"        {certificate_name} {logs_name} {values_name} :=",
                "  { logLower := by rfl'",
                "    logUpper := by rfl'",
                "    q := by rfl'",
                "    qPrime := by rfl' }",
                "",
                f"theorem {sound_name} :",
                f"    LRUpperKPointCache.Sound terms {z} {values_name} :=",
                "  LRUpperKLiteralCachedLogPointCertificate.sound_of_atomic_outer_eq",
                "    pointDyadicBits logDyadicBits",
                f"      terms {checks_name} {outer_equalities_name}",
                "",
                f"def {point_name} :",
                "    LRUpperKPointCache.CertifiedPoint terms",
                f"      {z} :=",
                f"  {{ values := {values_name}, sound := {sound_name} }}",
                "",
            ]
        )
        records.append(
            {
                "cacheId": entry.cache_id,
                "module": module,
                "namespace": namespace,
                "pointName": point_name,
                "qualifiedPointName": (
                    f"CourtadeKumar.{GENERATED_NAMESPACE}.{namespace}.{point_name}"
                ),
                "certificateName": certificate_name,
                "logsName": logs_name,
                "valuesName": values_name,
                "atomicChecksName": checks_name,
                "outerEqualitiesName": outer_equalities_name,
                "soundName": sound_name,
                "z": [entry.z.numerator, entry.z.denominator],
                "leafMultiplicity": entry.leaf_multiplicity,
                "firstUseOrdinal": entry.first_use_ordinal,
                "queryModule": entry.query_module,
                "queryIndex": entry.query_index,
            }
        )
    lines.extend(
        [
            f"end {namespace}",
            f"end CourtadeKumar.{GENERATED_NAMESPACE}",
            "",
        ]
    )
    # Joining encoded lines avoids ever allocating a module-sized two-byte
    # Python Unicode string solely because its rational type annotation is
    # written ``ℚ``.  UTF-8 encoding commutes with joining on ASCII newlines,
    # so these are exactly the bytes emitted by the previous implementation.
    source = b"\n".join(map(str.encode, lines))
    if source.count(b"rfl'") != 6 * len(entries):
        fail(f"{module} did not emit exactly six ordinary reductions per point")
    if source.count(b"norm_num [") != 4 * len(entries):
        fail(f"{module} did not emit exactly four norm_num proofs per point")
    if source.count(b"def point_") != len(entries):
        fail(f"{module} point declaration count drifted")
    return module, source, records


def validate_generated_byte_graph(sources: dict[str, bytes], prefix: str) -> None:
    """Byte-oriented form of the shared generated import-graph audit."""
    dependency_pattern = re.compile(rb"^import\s+(\S+)\s*$", re.MULTILINE)
    prefix_bytes = prefix.encode("ascii")
    graph: dict[str, list[str]] = {}
    for module, source in sources.items():
        dependencies = [
            dependency.decode("ascii")
            for dependency in dependency_pattern.findall(source)
            if dependency.startswith(prefix_bytes)
        ]
        missing = [
            dependency for dependency in dependencies if dependency not in sources
        ]
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


def validate_sources(
    sources: dict[str, bytes], prefix: str, expected_rfl: int,
    expected_norm_num: int,
) -> None:
    if not sources or len(sources) > MAX_GENERATED_MODULES:
        fail("generated fast point proof module count exceeds its hard guard")
    combined_bytes = 0
    reduction_count = 0
    norm_num_count = 0
    for module, source in sources.items():
        combined_bytes += len(source)
        reduction_count += source.count(b"rfl'")
        norm_num_count += source.count(b"norm_num [")
        if b"#eval" in source:
            fail(f"generated proof module {module} unexpectedly contains #eval")
        for forbidden in collection.query_plan.replay.FORBIDDEN_LEAN:
            if forbidden.encode("utf-8") in source:
                fail(
                    f"generated fast point proof contains forbidden token {forbidden!r}"
                )
    if combined_bytes > MAX_GENERATED_SOURCE_BYTES:
        fail("generated fast point proof source bytes exceed their hard guard")
    if reduction_count != expected_rfl:
        fail("generated fast point proof reduction count drifted")
    if norm_num_count != expected_norm_num:
        fail("generated fast point proof norm_num count drifted")
    validate_generated_byte_graph(sources, prefix)


def build(
    args: argparse.Namespace,
    query_manifest: dict[str, Any],
    query_manifest_bytes: bytes,
    receipt: dict[str, Any],
    receipt_bytes: bytes,
    entries: list[CacheEntry],
) -> tuple[dict[str, bytes], dict[str, object]]:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("fast point-cache proof generator changed before planning")
    prefix = proof_module_prefix(args.module_prefix)
    if len({entry.cache_id[:16] for entry in entries}) != len(entries):
        fail("fast point cache IDs collide at the audited 16-hex Lean-name prefix")

    query_implementation = query_manifest.get("implementation")
    if not isinstance(query_implementation, dict):
        fail("fast point-cache query implementation binding is malformed")
    proof_implementation = bind_point_proof_sources()
    parameters = query_manifest["parameters"]
    config_module, config_source = render_config(
        prefix,
        parameters,
        query_manifest,
        receipt,
        query_implementation,
        proof_implementation,
    )
    entry_count = len(entries)
    sources: dict[str, bytes] = {config_module: config_source.encode("utf-8")}
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
            fail(f"generated fast point-cache proof module collision: {module}")
        sources[module] = source
        proof_modules.append(module)
        entry_records.extend(records)
    # ``prepared`` gives this function sole ownership of ``entries``.  Its
    # ParsedValue/Fraction graph is no longer needed once every source literal
    # and compact manifest address has been rendered.  Releasing it before the
    # large manifest hash prevents those two representations from overlapping.
    entries.clear()
    import_sources: dict[str, str] = {}
    coverage, indexes = collection.query_plan.replay.add_import_fan_in(
        import_sources,
        prefix,
        "Coverage",
        proof_modules,
        args.max_imports_per_index,
    )
    for module, source in import_sources.items():
        if module in sources:
            fail(f"generated fast point-cache import module collision: {module}")
        sources[module] = source.encode("utf-8")
    validate_sources(sources, prefix, 6 * entry_count, 4 * entry_count)
    output_hashes = {
        f"{module}.lean": sha256_bytes(source)
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
            "evaluator": receipt.get("evaluator"),
        },
        "implementation": {
            "query": query_implementation,
            "pointProof": proof_implementation,
        },
        "proofApi": {
            "entryType": (
                "CourtadeKumar.LRUpperKPointCache.CertifiedPoint"
            ),
            "certificateType": "CourtadeKumar.LRQPointCertificate",
            "certificateCheck": (
                "CourtadeKumar.LRQPointCertificate.primeCheck"
            ),
            "atomicChecks": (
                "CourtadeKumar.LRQPointCertificate.AtomicChecks"
            ),
            "atomicPrimeCheckAssembly": (
                "CourtadeKumar.LRQPointCertificate.AtomicChecks.toPrimeCheck"
            ),
            "atomicRangeAssembly": (
                "CourtadeKumar.LRQPointCertificate.AtomicChecks.inRange"
            ),
            "cachedLogType": (
                "CourtadeKumar.LRUpperKCachedLogPointCertificate.LogValues"
            ),
            "cachedLogCovers": (
                "CourtadeKumar.LRUpperKCachedLogPointCertificate."
                "LogValues.Covers"
            ),
            "rawValues": (
                "CourtadeKumar.LRUpperKCachedLogPointCertificate.rawValues"
            ),
            "outerEnclosure": (
                "CourtadeKumar.LRUpperKDyadicOuterRounding.outerEnclosure"
            ),
            "outerEqualities": (
                "CourtadeKumar.LRUpperKLiteralCachedLogPointCertificate."
                "OuterEqualities"
            ),
            "soundness": (
                "CourtadeKumar.LRUpperKLiteralCachedLogPointCertificate."
                "sound_of_atomic_outer_eq"
            ),
            "outerEnclosureCovers": (
                "CourtadeKumar.LRUpperKDyadicOuterRounding."
                "outerEnclosure_covers"
            ),
            "coversRelation": (
                "CourtadeKumar.LRUpperKMidpointCoarsening.Covers"
            ),
        },
        "parameters": {
            **parameters,
            "proofsPerModule": args.proofs_per_module,
            "maxImportsPerIndex": args.max_imports_per_index,
            "maxRecDepth": args.max_rec_depth,
            "maxHeartbeats": args.max_heartbeats,
            "modulePrefix": prefix,
            "proofOrdering": (
                "query-manifest authenticated first-use order; no hash sorting"
            ),
            "proofStrategy": (
                "stack-safe six-atomic-check componentwise cached-log "
                "Q/Q-prime outer enclosure v4"
            ),
        },
        "outputDirectory": collection.query_plan.replay.relative_project_path(
            args.validated_output_dir
        ),
        "entryCount": entry_count,
        "certifiedPointCount": entry_count,
        "kernelArithmeticCheckCount": 10 * entry_count,
        "ordinaryRflReductionCount": 6 * entry_count,
        "normNumCertificateProofCount": 4 * entry_count,
        "atomicCertificateCheckCount": 6 * entry_count,
        "cachedLogEqualityReductionCount": 2 * entry_count,
        "pointValueEqualityReductionCount": 2 * entry_count,
        "standalonePointRangeProofCount": 0,
        "proofModuleCount": len(proof_modules),
        "proofModules": proof_modules,
        "importIndexModules": indexes,
        "coverageModule": coverage,
        "coverageImportPolicy": (
            "audit only; replay leaves import exact point proof modules instead"
        ),
        "collectedLogRangeDataPolicy": (
            "all four range-reduction records and both rounded sqrt endpoints "
            "are embedded in each literal LRQPointCertificate and checked as "
            "six independent arithmetic facts; both 40-bit cached logarithm "
            "enclosures are embedded separately, equality-checked against "
            "verified outward rounding once, and shared by Q and Q-prime"
        ),
        "literalDataLocation": (
            "certificate and enclosure literals occur only in authenticated Lean "
            "sources and bound collection outputs; the proof manifest keeps only "
            "the compact replay address map"
        ),
        "entries": entry_records,
        "leanModuleCount": len(sources),
        "outputs": output_hashes,
    }
    plan_sha = canonical_json_sha256(manifest_core)

    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("fast point-cache proof generator changed while rendering")
    if collection.query_plan.bind_fast_point_sources() != query_implementation.get(
        "fastPointCache"
    ):
        fail("fast point query implementation changed while proof plan rendered")
    if bind_point_proof_sources() != proof_implementation:
        fail("fast point proof implementation changed while proof plan rendered")
    validate_optional_evaluator(receipt, parameters)
    if read_regular_file(
        args.validated_query_manifest_path,
        "fast point-cache query manifest",
        collection.query_plan.MAX_MANIFEST_BYTES,
    ) != query_manifest_bytes:
        fail("fast point-cache query manifest changed while proof plan rendered")
    if read_regular_file(
        args.validated_collection_receipt_path,
        "fast point-cache collection receipt",
        MAX_RECEIPT_BYTES,
    ) != receipt_bytes:
        fail("fast point-cache collection receipt changed while proof plan rendered")
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
        "kernelArithmeticCheckCount": manifest["kernelArithmeticCheckCount"],
        "ordinaryRflReductionCount": manifest["ordinaryRflReductionCount"],
        "normNumCertificateProofCount": manifest[
            "normNumCertificateProofCount"
        ],
        "atomicCertificateCheckCount": manifest[
            "atomicCertificateCheckCount"
        ],
        "cachedLogEqualityReductionCount": manifest[
            "cachedLogEqualityReductionCount"
        ],
        "pointValueEqualityReductionCount": manifest[
            "pointValueEqualityReductionCount"
        ],
        "standalonePointRangeProofCount": manifest[
            "standalonePointRangeProofCount"
        ],
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
) -> tuple[dict[str, bytes], dict[str, object]]:
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
    # Only these three small authenticated fields are consulted by ``build``.
    # The selected/query/output tables have already been exhaustively checked
    # and copied into ``entries``; retaining them through source rendering used
    # hundreds of unnecessary megabytes.
    build_manifest = {
        "implementation": query_manifest["implementation"],
        "parameters": query_manifest["parameters"],
        "planSha256": query_manifest["planSha256"],
    }
    del modules, query_manifest, values
    args.validated_query_manifest_path = query_manifest_path
    args.validated_collection_receipt_path = receipt_path
    args.validated_output_dir = output_dir
    args.validated_output_identity = output_identity
    return build(
        args, build_manifest, query_bytes, receipt, receipt_bytes, entries
    )


def command_plan(args: argparse.Namespace) -> None:
    sources, manifest = prepared(args)
    del sources
    print(json.dumps(summary(manifest), indent=2, sort_keys=True))


def command_generate(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        fail("refusing fast point-cache proof emission without --confirm-write")
    sources, manifest = prepared(args)
    expected = collection.query_plan.replay.supplied_hex64(
        args.expected_plan_sha256, "--expected-plan-sha256"
    )
    if expected != manifest["planSha256"]:
        fail("--expected-plan-sha256 differs from the fresh fast point proof plan")
    directory: Path = args.validated_output_dir
    manifest_name = f"{proof_module_prefix(args.module_prefix)}Manifest.json"
    # Transfer ownership into the output transaction without duplicating the
    # complete byte corpus.  The writer sorts paths itself, so dictionary
    # insertion order carries no semantics.
    outputs: dict[Path, bytes] = {}
    while sources:
        module, source = sources.popitem()
        path = collection.query_plan.replay.safe_output_path(
            directory, f"{module}.lean"
        )
        outputs[path] = source
    manifest_path = collection.query_plan.replay.safe_output_path(
        directory, manifest_name
    )
    outputs[manifest_path] = pretty_json_bytes(manifest)
    collisions = [path.name for path in outputs if path.exists() or path.is_symlink()]
    if collisions:
        fail(
            "refusing to overwrite fast point-cache proof outputs: "
            f"{sorted(collisions)}"
        )
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
        "--module-prefix", default="AgentUpperKFastPointCacheProofGenerated"
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="authenticate and plan without writing")
    add_arguments(plan)
    plan.set_defaults(handler=command_plan)
    generate = commands.add_parser(
        "generate", help="emit kernel-authenticated fast point proof modules"
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
