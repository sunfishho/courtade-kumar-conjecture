#!/usr/bin/env python3
"""Collect bounded upper-``K`` fast point-cache query output serially.

The fast point query generator emits one raw, tab-separated row for each
selected positive argument of ``Q``/``Q'``.  This collector authenticates the
query manifest and every generated Lean source before running anything.  It
then runs at most one resource-bounded Lean process at a time, parses the
rounded square-root interval, all four logarithm range reductions, both cached
logarithm enclosures, and the rounded ``Q``/``Q'`` intervals with a strict
canonical-number grammar.  Each module's output is written by exclusive
creation; existing valid outputs make the operation resumable.

The collection receipt commits to the output files and to a canonical JSON
stream of parsed values in manifest order.  The stream is hashed incrementally
so the collector never retains all parsed results in memory.  Both the Python
parser and the resulting data remain untrusted: a later generated Lean proof
must authenticate every literal using ordinary kernel-checked reduction.
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


sys.dont_write_bytecode = True

import generate_lr_upper_k_fast_point_cache_queries as query_plan


SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
CHECKER = SCRATCH / "AgentRepoLocalLeanCheck.sh"
HEX64_PATTERN = re.compile(r"[0-9a-f]{64}")
INTEGER_PATTERN = re.compile(rb"-?(?:0|[1-9][0-9]*)")
RATIONAL_PATTERN = re.compile(
    rb"(-?(?:0|[1-9][0-9]*))(?: / ([1-9][0-9]*))?"
)
EXPECTED_QUERY_ROW_SCHEMA = "upper-k-fast-point-cache-query-row-v3"
EXPECTED_PLAN_FORMAT = "authenticated patched upper-K fast point-cache query plan v3"
EXPECTED_CACHE_KEY_SCHEMA = "upper-k-fast-point-cache-key-v2"
EXPECTED_CERTIFICATE_SCHEME = (
    "lr-q-small-range-binomial-six-plus-y7-lower-rounded-sqrt-log-v1"
)
QUERY_COLUMNS = (
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
)
MAX_SOURCE_BYTES = 2 * 1024 * 1024
MAX_STDOUT_BYTES = 4 * 1024 * 1024
MAX_STDERR_BYTES = 2 * 1024 * 1024
MAX_ATOMIC_FIELD_BYTES = 4 * 1024
MAX_CHECKER_BYTES = 64 * 1024
MAX_MANIFEST_BYTES = query_plan.MAX_MANIFEST_BYTES
RECEIPT_FORMAT = "authenticated upper-K fast point-cache query collection v3"
RESULT_SET_HASH_ALGORITHM = (
    "sha256 of the canonical JSON array of ParsedValue.record() objects in "
    "query-manifest module/row order, streamed without whitespace"
)


@dataclass(frozen=True, slots=True)
class ExpectedPoint:
    cache_id: str
    z: Fraction


@dataclass(frozen=True, slots=True)
class ParsedValue:
    cache_id: str
    z: Fraction
    sqrt_lower: Fraction
    sqrt_upper: Fraction
    log_lower_lower_exponent: int
    log_lower_lower_mantissa: Fraction
    log_lower_upper_exponent: int
    log_lower_upper_mantissa: Fraction
    log_upper_lower_exponent: int
    log_upper_lower_mantissa: Fraction
    log_upper_upper_exponent: int
    log_upper_upper_mantissa: Fraction
    log_lower_enclosure_lower: Fraction
    log_lower_enclosure_upper: Fraction
    log_upper_enclosure_lower: Fraction
    log_upper_enclosure_upper: Fraction
    q_lower: Fraction
    q_upper: Fraction
    q_prime_lower: Fraction
    q_prime_upper: Fraction

    def record(self) -> dict[str, object]:
        return {
            "cacheId": self.cache_id,
            "z": fraction_record(self.z),
            "sqrt": {
                "lower": fraction_record(self.sqrt_lower),
                "upper": fraction_record(self.sqrt_upper),
            },
            "logLowerProbability": {
                "lower": {
                    "exponent": self.log_lower_lower_exponent,
                    "mantissa": fraction_record(
                        self.log_lower_lower_mantissa
                    ),
                },
                "upper": {
                    "exponent": self.log_lower_upper_exponent,
                    "mantissa": fraction_record(
                        self.log_lower_upper_mantissa
                    ),
                },
            },
            "logUpperProbability": {
                "lower": {
                    "exponent": self.log_upper_lower_exponent,
                    "mantissa": fraction_record(
                        self.log_upper_lower_mantissa
                    ),
                },
                "upper": {
                    "exponent": self.log_upper_upper_exponent,
                    "mantissa": fraction_record(
                        self.log_upper_upper_mantissa
                    ),
                },
            },
            "logLowerEnclosure": {
                "lower": fraction_record(self.log_lower_enclosure_lower),
                "upper": fraction_record(self.log_lower_enclosure_upper),
            },
            "logUpperEnclosure": {
                "lower": fraction_record(self.log_upper_enclosure_lower),
                "upper": fraction_record(self.log_upper_enclosure_upper),
            },
            "q": {
                "lower": fraction_record(self.q_lower),
                "upper": fraction_record(self.q_upper),
            },
            "qPrime": {
                "lower": fraction_record(self.q_prime_lower),
                "upper": fraction_record(self.q_prime_upper),
            },
        }


def fail(message: str) -> None:
    raise query_plan.replay.ReplayPlanError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return query_plan.canonical_json_bytes(value)


def pretty_json_bytes(value: object) -> bytes:
    return query_plan.pretty_json_bytes(value)


def fraction_record(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def read_regular_file(path: Path, context: str, maximum: int) -> bytes:
    return query_plan.replay.read_regular_file(path, context, maximum)


def strict_int(value: object, context: str, minimum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        fail(f"{context} is not an integer")
    if minimum is not None and value < minimum:
        fail(f"{context} is below {minimum}")
    return value


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
    if fraction_record(result) != value:
        fail(f"{context} is not reduced with a positive denominator")
    return result


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


def expected_query_output_record() -> dict[str, object]:
    return {
        "schema": EXPECTED_QUERY_ROW_SCHEMA,
        "transport": (
            "one raw ASCII-TAB-separated line per point from one #eval per module; "
            "all non-ID fields are atomic Lean Repr values"
        ),
        "separator": "ASCII TAB",
        "columnCount": len(QUERY_COLUMNS),
        "columns": list(QUERY_COLUMNS),
    }


def strict_parameters(manifest: dict[str, Any]) -> dict[str, Any]:
    parameters = manifest.get("parameters")
    expected_keys = {
        "cacheKeySchema",
        "certificateScheme",
        "pointDyadicBits",
        "logDyadicBits",
        "sqrtDyadicBits",
        "terms",
        "logFuel",
        "cacheMultiplicityThreshold",
        "queriesPerModule",
        "modulePrefix",
        "queryOrdering",
    }
    if not isinstance(parameters, dict) or set(parameters) != expected_keys:
        fail("fast point-cache query parameters have an unexpected schema")
    if parameters["cacheKeySchema"] != EXPECTED_CACHE_KEY_SCHEMA:
        fail("fast point-cache key schema drifted")
    if parameters["certificateScheme"] != EXPECTED_CERTIFICATE_SCHEME:
        fail("fast point-cache certificate scheme drifted")
    point_bits = strict_int(
        parameters["pointDyadicBits"], "parameters.pointDyadicBits", 1
    )
    log_bits = strict_int(
        parameters["logDyadicBits"], "parameters.logDyadicBits", 1
    )
    sqrt_bits = strict_int(
        parameters["sqrtDyadicBits"], "parameters.sqrtDyadicBits", 8
    )
    if point_bits > 256 or log_bits > 256 or sqrt_bits > 128:
        fail("fast point-cache dyadic precision exceeds the supported guard")
    if log_bits != point_bits:
        fail("v3 requires equal point and cached-log dyadic precisions")
    strict_int(parameters["terms"], "parameters.terms", 1)
    strict_int(parameters["logFuel"], "parameters.logFuel", 1)
    strict_int(
        parameters["cacheMultiplicityThreshold"],
        "parameters.cacheMultiplicityThreshold",
        1,
    )
    queries_per_module = strict_int(
        parameters["queriesPerModule"], "parameters.queriesPerModule", 1
    )
    if queries_per_module > 64:
        fail("parameters.queriesPerModule exceeds the generator guard")
    prefix = parameters["modulePrefix"]
    if not isinstance(prefix, str):
        fail("parameters.modulePrefix is not a string")
    query_plan.query_module_prefix(prefix)
    if parameters["queryOrdering"] != (
        "authenticated root/frontier first use, ascending rational within leaf"
    ):
        fail("fast point-cache query ordering identity drifted")
    return parameters


def strict_manifest(path: Path, query_dir: Path) -> dict[str, Any]:
    if query_plan.QUERY_ROW_SCHEMA != EXPECTED_QUERY_ROW_SCHEMA:
        fail("collector and fast point query generator disagree on row schema v3")
    if query_plan.FORMAT != EXPECTED_PLAN_FORMAT:
        fail("collector and fast point query generator disagree on plan format v3")
    if query_plan.CACHE_KEY_SCHEMA != EXPECTED_CACHE_KEY_SCHEMA:
        fail("collector and fast point query generator disagree on cache-key schema v2")
    if query_plan.FAST_CERTIFICATE_SCHEME != EXPECTED_CERTIFICATE_SCHEME:
        fail("collector and fast point query generator disagree on certificate scheme")
    data = read_regular_file(
        path, "fast point-cache query manifest", MAX_MANIFEST_BYTES
    )
    try:
        manifest = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse fast point-cache query manifest: {error}")
    if not isinstance(manifest, dict):
        fail("fast point-cache query manifest must be a JSON object")
    if data != pretty_json_bytes(manifest):
        fail("fast point-cache query manifest is not canonical generated JSON")
    plan_sha = manifest.get("planSha256")
    if not isinstance(plan_sha, str) or HEX64_PATTERN.fullmatch(plan_sha) is None:
        fail("fast point-cache query manifest has an invalid planSha256")
    core = dict(manifest)
    del core["planSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != plan_sha:
        fail("fast point-cache query manifest plan hash is invalid")
    if manifest.get("format") != EXPECTED_PLAN_FORMAT:
        fail("fast point-cache query manifest format drifted")
    if manifest.get("proofAuthority") != query_plan.PROOF_AUTHORITY:
        fail("fast point-cache query proof-authority declaration drifted")
    if manifest.get("queryOutput") != expected_query_output_record():
        fail("fast point-cache query row schema or transport drifted")
    expected_directory = query_plan.replay.relative_project_path(query_dir)
    if manifest.get("outputDirectory") != expected_directory:
        fail("query directory differs from the manifest outputDirectory")

    expected_generator = {
        "file": query_plan.SCRIPT.name,
        "byteSha256": query_plan.SCRIPT_BYTE_SHA256,
        "directReplayGeneratorFile": query_plan.replay.SCRIPT.name,
        "directReplayGeneratorByteSha256": query_plan.replay.SCRIPT_BYTE_SHA256,
        "scalarGeometryGeneratorFile": query_plan.scalar_geometry.SCRIPT.name,
        "scalarGeometryGeneratorByteSha256": (
            query_plan.scalar_geometry.SCRIPT_BYTE_SHA256
        ),
    }
    if manifest.get("generator") != expected_generator:
        fail("query manifest is not bound to the current committed generators")
    expected_implementation = {
        "directReplay": query_plan.replay.bind_direct_replay_sources(),
        "fastPointCache": query_plan.bind_fast_point_sources(),
    }
    if manifest.get("implementation") != expected_implementation:
        fail("fast point-cache implementation binding is stale")
    strict_parameters(manifest)
    return manifest


def cache_identifier(point: Fraction, parameters: dict[str, Any]) -> str:
    payload = {
        "schema": parameters["cacheKeySchema"],
        "certificateScheme": parameters["certificateScheme"],
        "z": fraction_record(point),
        "pointDyadicBits": parameters["pointDyadicBits"],
        "logDyadicBits": parameters["logDyadicBits"],
        "sqrtDyadicBits": parameters["sqrtDyadicBits"],
        "terms": parameters["terms"],
        "logFuel": parameters["logFuel"],
    }
    return sha256_bytes(canonical_json_bytes(payload))


def expected_modules(
    manifest: dict[str, Any], query_dir: Path
) -> list[tuple[str, Path, list[ExpectedPoint]]]:
    outputs = manifest.get("outputs")
    queries = manifest.get("queries")
    selected = manifest.get("selected")
    if not isinstance(outputs, dict) or not isinstance(queries, list) or not isinstance(
        selected, list
    ):
        fail("fast point-cache query output tables are malformed")
    module_count = strict_int(
        manifest.get("queryModuleCount"), "queryModuleCount", 0
    )
    selected_count = strict_int(
        manifest.get("selectedPointKeys"), "selectedPointKeys", 0
    )
    if len(outputs) != module_count or len(queries) != module_count:
        fail("fast point-cache query module counts disagree")
    if len(selected) != selected_count:
        fail("fast point-cache selected-point count disagrees")
    if selected_count == 0 or module_count == 0:
        fail("fast point-cache query plan is unexpectedly empty")

    parameters = strict_parameters(manifest)
    threshold = parameters["cacheMultiplicityThreshold"]
    selected_points: list[tuple[str, ExpectedPoint, int, int]] = []
    seen_ids: set[str] = set()
    seen_points: set[Fraction] = set()
    previous_first_use = -1
    selected_occurrences = 0
    expected_selected_keys = {
        "cacheId",
        "z",
        "leafMultiplicity",
        "firstUseOrdinal",
        "queryModule",
        "queryIndex",
    }
    for ordinal, record in enumerate(selected):
        if not isinstance(record, dict) or set(record) != expected_selected_keys:
            fail(f"query manifest selected[{ordinal}] has an unexpected schema")
        identifier = record["cacheId"]
        module = record["queryModule"]
        index = record["queryIndex"]
        multiplicity = record["leafMultiplicity"]
        first_use = record["firstUseOrdinal"]
        if (
            not isinstance(identifier, str)
            or HEX64_PATTERN.fullmatch(identifier) is None
            or not isinstance(module, str)
        ):
            fail(f"query manifest selected[{ordinal}] has invalid addressing")
        strict_int(index, f"selected[{ordinal}].queryIndex", 0)
        strict_int(multiplicity, f"selected[{ordinal}].leafMultiplicity", threshold)
        strict_int(first_use, f"selected[{ordinal}].firstUseOrdinal", 0)
        if first_use <= previous_first_use:
            fail("selected fast point rows are not in strict first-use order")
        previous_first_use = first_use
        point = fraction_from_record(record["z"], f"selected[{ordinal}].z")
        if not Fraction(0) < point <= Fraction(1, 16):
            fail(f"selected[{ordinal}].z escaped the authenticated point domain")
        if cache_identifier(point, parameters) != identifier:
            fail(f"selected[{ordinal}] cache ID does not hash its exact point key")
        if identifier in seen_ids:
            fail("query manifest repeats a selected cache ID")
        if point in seen_points:
            fail("query manifest repeats a selected rational point")
        seen_ids.add(identifier)
        seen_points.add(point)
        selected_occurrences += multiplicity
        selected_points.append((module, ExpectedPoint(identifier, point), index, ordinal))

    if selected_occurrences != strict_int(
        manifest.get("selectedPointLeafOccurrences"),
        "selectedPointLeafOccurrences",
        selected_count,
    ):
        fail("selected point multiplicities disagree with their manifest total")

    by_module: dict[str, list[tuple[int, ExpectedPoint, int]]] = {}
    for module, point, index, ordinal in selected_points:
        by_module.setdefault(module, []).append((index, point, ordinal))

    prefix = parameters["modulePrefix"]
    result: list[tuple[str, Path, list[ExpectedPoint]]] = []
    seen_modules: set[str] = set()
    flattened_ordinals: list[int] = []
    expected_query_keys = {
        "module",
        "firstCacheId",
        "lastCacheId",
        "queryCount",
        "streamingEvalCount",
    }
    for ordinal, query in enumerate(queries):
        if not isinstance(query, dict) or set(query) != expected_query_keys:
            fail(f"query manifest queries[{ordinal}] has an unexpected schema")
        module = query["module"]
        expected_module = f"{prefix}Q{ordinal:04d}"
        if module != expected_module:
            fail(
                f"fast point query modules are missing or misordered at ordinal {ordinal}"
            )
        if module in seen_modules:
            fail("fast point query manifest repeats a module")
        seen_modules.add(module)
        count = strict_int(query["queryCount"], f"queries[{ordinal}].queryCount", 1)
        if count > parameters["queriesPerModule"]:
            fail(f"query count exceeds the module bound for {module}")
        if query["streamingEvalCount"] != 1:
            fail(f"streaming #eval count drifted for {module}")
        filename = f"{module}.lean"
        expected_hash = outputs.get(filename)
        if not isinstance(expected_hash, str) or HEX64_PATTERN.fullmatch(
            expected_hash
        ) is None:
            fail(f"query manifest lacks an output hash for {filename}")
        source = query_dir / filename
        source_bytes = read_regular_file(
            source, f"fast point query source {filename}", MAX_SOURCE_BYTES
        )
        if sha256_bytes(source_bytes) != expected_hash:
            fail(f"fast point query source hash drifted for {filename}")
        entries = sorted(by_module.get(module, []), key=lambda item: item[0])
        if [index for index, _point, _ordinal in entries] != list(range(count)):
            fail(f"query indexes are missing, duplicated, or noncontiguous for {module}")
        points = [point for _index, point, _ordinal in entries]
        flattened_ordinals.extend(entry_ordinal for _index, _point, entry_ordinal in entries)
        if points[0].cache_id != query["firstCacheId"] or points[-1].cache_id != query[
            "lastCacheId"
        ]:
            fail(f"query endpoint cache IDs drifted for {module}")
        result.append((module, source, points))

    if flattened_ordinals != list(range(selected_count)):
        fail("selected point rows are assigned to missing or misordered modules")
    if seen_modules != set(by_module) or set(outputs) != {
        f"{module}.lean" for module in seen_modules
    }:
        fail("query modules, selected points, and source outputs disagree")
    return result


def parse_integer(field: bytes, context: str) -> int:
    if len(field) > MAX_ATOMIC_FIELD_BYTES:
        fail(f"{context} exceeds the atomic-field byte guard")
    if INTEGER_PATTERN.fullmatch(field) is None:
        fail(f"{context} is not a canonical Lean integer representation")
    value = int(field)
    if field != str(value).encode("ascii"):
        fail(f"{context} is not a canonical Lean integer representation")
    return value


def parse_rational(field: bytes, context: str) -> Fraction:
    if len(field) > MAX_ATOMIC_FIELD_BYTES:
        fail(f"{context} exceeds the atomic-field byte guard")
    match = RATIONAL_PATTERN.fullmatch(field)
    if match is None:
        fail(f"{context} is not a canonical Lean rational representation")
    value = Fraction(
        int(match.group(1)), int(match.group(2)) if match.group(2) is not None else 1
    )
    rendered = str(value.numerator)
    if value.denominator != 1:
        rendered += f" / {value.denominator}"
    if field != rendered.encode("ascii"):
        fail(f"{context} is not reduced canonical Lean rational syntax")
    return value


def validate_dyadic_endpoint(value: Fraction, bits: int, context: str) -> None:
    denominator = value.denominator
    if denominator > 1 << bits or denominator & (denominator - 1) != 0:
        fail(f"{context} is not a dyadic at the declared point precision")


def parse_output(
    data: bytes, expected_points: list[ExpectedPoint], parameters: dict[str, Any]
) -> list[ParsedValue]:
    if len(data) > MAX_STDOUT_BYTES:
        fail("fast point query stdout exceeds the hard byte guard")
    if not data.endswith(b"\n"):
        fail("fast point query stdout is not newline terminated")
    lines = data.splitlines()
    if len(lines) != len(expected_points):
        fail("fast point query stdout line count differs from the manifest")
    values: list[ParsedValue] = []
    bits = parameters["pointDyadicBits"]
    log_bits = parameters["logDyadicBits"]
    for row_index, (line, expected) in enumerate(
        zip(lines, expected_points, strict=True)
    ):
        fields = line.split(b"\t")
        if len(fields) != len(QUERY_COLUMNS):
            fail(
                f"fast point stdout row {row_index} has {len(fields)} atomic fields; "
                f"expected {len(QUERY_COLUMNS)}"
            )
        try:
            identifier = fields[0].decode("ascii")
        except UnicodeDecodeError as error:
            fail(f"fast point stdout row {row_index} has a non-ASCII cache ID: {error}")
        if identifier != expected.cache_id:
            fail(f"fast point stdout cache-ID order drifted at row {row_index}")
        point = parse_rational(fields[1], f"row {row_index} z")
        if point != expected.z:
            fail(f"fast point stdout z differs from its manifest key at row {row_index}")
        value = ParsedValue(
            cache_id=identifier,
            z=point,
            sqrt_lower=parse_rational(fields[2], f"row {row_index} sqrt.lower"),
            sqrt_upper=parse_rational(fields[3], f"row {row_index} sqrt.upper"),
            log_lower_lower_exponent=parse_integer(
                fields[4], f"row {row_index} logLower.lower.exponent"
            ),
            log_lower_lower_mantissa=parse_rational(
                fields[5], f"row {row_index} logLower.lower.mantissa"
            ),
            log_lower_upper_exponent=parse_integer(
                fields[6], f"row {row_index} logLower.upper.exponent"
            ),
            log_lower_upper_mantissa=parse_rational(
                fields[7], f"row {row_index} logLower.upper.mantissa"
            ),
            log_upper_lower_exponent=parse_integer(
                fields[8], f"row {row_index} logUpper.lower.exponent"
            ),
            log_upper_lower_mantissa=parse_rational(
                fields[9], f"row {row_index} logUpper.lower.mantissa"
            ),
            log_upper_upper_exponent=parse_integer(
                fields[10], f"row {row_index} logUpper.upper.exponent"
            ),
            log_upper_upper_mantissa=parse_rational(
                fields[11], f"row {row_index} logUpper.upper.mantissa"
            ),
            log_lower_enclosure_lower=parse_rational(
                fields[12], f"row {row_index} logLowerEnclosure.lower"
            ),
            log_lower_enclosure_upper=parse_rational(
                fields[13], f"row {row_index} logLowerEnclosure.upper"
            ),
            log_upper_enclosure_lower=parse_rational(
                fields[14], f"row {row_index} logUpperEnclosure.lower"
            ),
            log_upper_enclosure_upper=parse_rational(
                fields[15], f"row {row_index} logUpperEnclosure.upper"
            ),
            q_lower=parse_rational(fields[16], f"row {row_index} q.lower"),
            q_upper=parse_rational(fields[17], f"row {row_index} q.upper"),
            q_prime_lower=parse_rational(
                fields[18], f"row {row_index} qPrime.lower"
            ),
            q_prime_upper=parse_rational(
                fields[19], f"row {row_index} qPrime.upper"
            ),
        )
        if value.sqrt_lower > value.sqrt_upper:
            fail(f"fast point stdout sqrt interval is reversed for {identifier}")
        if value.log_lower_enclosure_lower > value.log_lower_enclosure_upper:
            fail(
                f"fast point stdout logLowerEnclosure is reversed for {identifier}"
            )
        if value.log_upper_enclosure_lower > value.log_upper_enclosure_upper:
            fail(
                f"fast point stdout logUpperEnclosure is reversed for {identifier}"
            )
        if value.q_lower > value.q_upper:
            fail(f"fast point stdout q interval is reversed for {identifier}")
        if value.q_prime_lower > value.q_prime_upper:
            fail(f"fast point stdout qPrime interval is reversed for {identifier}")
        sqrt_bits = parameters["sqrtDyadicBits"]
        validate_dyadic_endpoint(
            value.sqrt_lower, sqrt_bits, f"row {row_index} sqrt.lower"
        )
        validate_dyadic_endpoint(
            value.sqrt_upper, sqrt_bits, f"row {row_index} sqrt.upper"
        )
        validate_dyadic_endpoint(
            value.log_lower_enclosure_lower,
            log_bits,
            f"row {row_index} logLowerEnclosure.lower",
        )
        validate_dyadic_endpoint(
            value.log_lower_enclosure_upper,
            log_bits,
            f"row {row_index} logLowerEnclosure.upper",
        )
        validate_dyadic_endpoint(
            value.log_upper_enclosure_lower,
            log_bits,
            f"row {row_index} logUpperEnclosure.lower",
        )
        validate_dyadic_endpoint(
            value.log_upper_enclosure_upper,
            log_bits,
            f"row {row_index} logUpperEnclosure.upper",
        )
        validate_dyadic_endpoint(value.q_lower, bits, f"row {row_index} q.lower")
        validate_dyadic_endpoint(value.q_upper, bits, f"row {row_index} q.upper")
        validate_dyadic_endpoint(
            value.q_prime_lower, bits, f"row {row_index} qPrime.lower"
        )
        validate_dyadic_endpoint(
            value.q_prime_upper, bits, f"row {row_index} qPrime.upper"
        )
        values.append(value)
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
    path: Path, expected: list[ExpectedPoint], parameters: dict[str, Any]
) -> tuple[bytes, list[ParsedValue]]:
    data = read_regular_file(path, f"collected output {path.name}", MAX_STDOUT_BYTES)
    return data, parse_output(data, expected, parameters)


def update_result_set_hash(
    hasher: Any, values: list[ParsedValue], first_record: bool
) -> tuple[bool, int]:
    count = 0
    for value in values:
        if not first_record:
            hasher.update(b",")
        hasher.update(canonical_json_bytes(value.record()))
        first_record = False
        count += 1
    return first_record, count


def reject_unexpected_output_files(
    output_dir: Path, expected_names: set[str], receipt_name: str
) -> None:
    for candidate in output_dir.iterdir():
        if candidate.name == receipt_name:
            continue
        if candidate.suffix == ".out" and candidate.name not in expected_names:
            fail(f"output directory contains unexpected module output {candidate.name}")
        if candidate.name.endswith("CollectionReceipt.json"):
            fail(f"output directory contains an unexpected receipt {candidate.name}")


def collect(args: argparse.Namespace) -> None:
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("fast point collector changed before execution")
    query_plan.replay.validate_repository_location()
    query_dir, _query_identity = scratch_directory(args.query_dir, "--query-dir")
    output_dir, output_identity = scratch_directory(args.output_dir, "--output-dir")
    manifest_path = query_plan.replay.project_path(
        args.query_manifest, "--query-manifest"
    )
    if manifest_path.parent != query_dir:
        fail("--query-manifest must be directly inside --query-dir")
    manifest = strict_manifest(manifest_path, query_dir)
    manifest_bytes = read_regular_file(
        manifest_path, "fast point-cache query manifest", MAX_MANIFEST_BYTES
    )
    try:
        if json.loads(manifest_bytes) != manifest:
            fail("fast point-cache query manifest changed during authentication")
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot reparse fast point-cache query manifest: {error}")
    modules = expected_modules(manifest, query_dir)
    parameters = strict_parameters(manifest)
    if args.max_modules < 1:
        fail("--max-modules must be positive")
    if args.timeout_seconds < 1:
        fail("--timeout-seconds must be positive")
    if not CHECKER.is_file() or CHECKER.is_symlink():
        fail("repository-local Lean checker is missing or not a regular file")
    checker_bytes = read_regular_file(
        CHECKER, "repository-local Lean checker", MAX_CHECKER_BYTES
    )

    output_metadata = output_dir.stat()
    if (output_metadata.st_dev, output_metadata.st_ino) != output_identity:
        fail("--output-dir identity changed before collection")
    receipt_name = f"{parameters['modulePrefix']}CollectionReceipt.json"
    expected_output_names = {f"{module}.out" for module, _source, _ids in modules}
    reject_unexpected_output_files(output_dir, expected_output_names, receipt_name)

    processed = 0
    reused = 0
    started = time.monotonic()
    for ordinal, (module, source, expected) in enumerate(modules):
        output = output_dir / f"{module}.out"
        if output.exists() or output.is_symlink():
            validate_existing_output(output, expected, parameters)
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
            fail(f"Lean fast point query timed out for {module}: {error}")
        if len(result.stderr) > MAX_STDERR_BYTES:
            fail(f"Lean fast point query stderr exceeded its guard for {module}")
        if result.returncode != 0:
            diagnostic = result.stderr.decode("utf-8", errors="replace")[-4000:]
            fail(f"Lean fast point query failed for {module}: {diagnostic}")
        parse_output(result.stdout, expected, parameters)
        exclusive_write(output, result.stdout, output_identity)
        if not args.keep_lean_artifacts:
            remove_lean_artifacts(source)
        processed += 1
        print(
            json.dumps(
                {
                    "status": "collected",
                    "module": module,
                    "ordinal": ordinal,
                    "completedModules": reused + processed,
                    "totalModules": len(modules),
                    "queries": len(expected),
                    "seconds": round(time.monotonic() - module_started, 3),
                },
                sort_keys=True,
            ),
            flush=True,
        )

    all_outputs: dict[str, dict[str, object]] = {}
    missing: list[str] = []
    result_hasher = hashlib.sha256()
    result_hasher.update(b"[")
    first_record = True
    value_count = 0
    seen_result_ids: set[str] = set()
    for module, _source, expected in modules:
        output = output_dir / f"{module}.out"
        if not output.exists() or output.is_symlink():
            missing.append(module)
            continue
        data, values = validate_existing_output(output, expected, parameters)
        for value in values:
            if value.cache_id in seen_result_ids:
                fail("complete fast point collection repeats a cache ID")
            seen_result_ids.add(value.cache_id)
        first_record, added = update_result_set_hash(
            result_hasher, values, first_record
        )
        value_count += added
        all_outputs[output.name] = {
            "bytes": len(data),
            "byteSha256": sha256_bytes(data),
            "queryCount": len(values),
        }

    if missing:
        if (output_dir / receipt_name).exists() or (
            output_dir / receipt_name
        ).is_symlink():
            fail("a complete receipt exists while module outputs are missing")
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

    result_hasher.update(b"]")
    if value_count != manifest["selectedPointKeys"]:
        fail("complete fast point collection count disagrees with query manifest")
    if len(seen_result_ids) != value_count:
        fail("complete fast point collection cache-ID uniqueness drifted")

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
            "byteSha256": sha256_bytes(manifest_bytes),
            "planSha256": manifest["planSha256"],
        },
        "certificateScheme": parameters["certificateScheme"],
        "moduleCount": len(modules),
        "valueCount": value_count,
        "resultSetHashAlgorithm": RESULT_SET_HASH_ALGORITHM,
        "resultSetSha256": result_hasher.hexdigest(),
        "outputs": dict(sorted(all_outputs.items())),
    }
    receipt = {
        **receipt_core,
        "receiptPayloadSha256": sha256_bytes(canonical_json_bytes(receipt_core)),
    }
    receipt_path = output_dir / receipt_name
    rendered = pretty_json_bytes(receipt)
    if sha256_bytes(SCRIPT.read_bytes()) != SCRIPT_BYTE_SHA256:
        fail("fast point collector changed during execution")
    if read_regular_file(
        manifest_path, "fast point-cache query manifest", MAX_MANIFEST_BYTES
    ) != manifest_bytes:
        fail("fast point-cache query manifest changed during collection")
    if sha256_bytes(query_plan.SCRIPT.read_bytes()) != query_plan.SCRIPT_BYTE_SHA256:
        fail("fast point query generator changed during collection")
    if (
        sha256_bytes(query_plan.replay.SCRIPT.read_bytes())
        != query_plan.replay.SCRIPT_BYTE_SHA256
    ):
        fail("direct replay generator changed during fast point collection")
    if (
        sha256_bytes(query_plan.scalar_geometry.SCRIPT.read_bytes())
        != query_plan.scalar_geometry.SCRIPT_BYTE_SHA256
    ):
        fail("scalar geometry generator changed during fast point collection")
    if manifest["implementation"] != {
        "directReplay": query_plan.replay.bind_direct_replay_sources(),
        "fastPointCache": query_plan.bind_fast_point_sources(),
    }:
        fail("fast point implementation changed during collection")
    if read_regular_file(
        CHECKER, "repository-local Lean checker", MAX_CHECKER_BYTES
    ) != checker_bytes:
        fail("repository-local Lean checker changed during execution")
    if receipt_path.exists() or receipt_path.is_symlink():
        existing = read_regular_file(
            receipt_path,
            "fast point-cache collection receipt",
            MAX_MANIFEST_BYTES,
        )
        if existing != rendered:
            fail("existing complete fast point collection receipt differs")
    else:
        exclusive_write(receipt_path, rendered, output_identity)
    print(
        json.dumps(
            {
                "status": "complete",
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
