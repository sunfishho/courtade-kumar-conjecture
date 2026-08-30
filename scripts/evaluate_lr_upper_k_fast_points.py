#!/usr/bin/env python3
"""Evaluate the rounded upper-``K`` point payload with exact Python rationals.

This is a deliberately untrusted acceleration layer.  It is a direct port of
the executable definitions used by
``LRQFastPointCertificate.roundedAuto`` and the cached-log
``LRUpperKCachedLogPointCore.rawValues``/``outerValues`` path.  Its output only
proposes the literal square-root/logarithm certificate, cached logarithm
outers, and rounded ``Q``/``Q'`` endpoints; ordinary Lean kernel reduction
must still check every generated certificate.

The expensive part of the old query pipeline was asking Lean to evaluate the
same closed rational program tens of thousands of times.  Python's
``fractions.Fraction`` has the same normalized rational semantics needed here,
so this program can produce byte-for-byte compatible atomic ``reprStr`` fields
without contributing any proof authority.

Two commands are provided:

* ``point`` evaluates one rational point and prints a tab-separated row; and
* ``evaluate-manifest`` authenticates a generated fast-point query manifest
  and fills its module ``.out`` files without running Lean.

The manifest command supports the original fourteen-column query schema, the
sixteen-column literal-certificate schema, and the preferred twenty-column
schema that also stores a 40-bit outward rounding of both exact log
enclosures.  Existing output files are reused only when their bytes agree
exactly with a fresh evaluation, making the command safely resumable.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import re
import stat
import sys
import time
from typing import Any, Iterable


sys.dont_write_bytecode = True

import generate_lr_upper_k_fast_point_cache_queries as query_plan


SCRIPT = Path(__file__).resolve()
REPOSITORY = SCRIPT.parent.parent.resolve()
SCRATCH = (REPOSITORY / ".lake" / "scratch").resolve()
SCRIPT_BYTE_SHA256 = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
MAX_MANIFEST_BYTES = 64 * 1024 * 1024
MAX_SOURCE_BYTES = 2 * 1024 * 1024
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
HEX64_PATTERN = re.compile(r"[0-9a-f]{64}")


ORIGINAL_COLUMNS = (
    "cacheId",
    "z",
    "logLower.lower.exponent",
    "logLower.lower.mantissa",
    "logLower.upper.exponent",
    "logLower.upper.mantissa",
    "logUpper.lower.exponent",
    "logUpper.lower.mantissa",
    "logUpper.upper.exponent",
    "logUpper.upper.mantissa",
    "q.lower",
    "q.upper",
    "qPrime.lower",
    "qPrime.upper",
)

FULL_CERTIFICATE_COLUMNS = (
    "cacheId",
    "z",
    "sqrtOneSub.lower",
    "sqrtOneSub.upper",
    "logLower.lower.exponent",
    "logLower.lower.mantissa",
    "logLower.upper.exponent",
    "logLower.upper.mantissa",
    "logUpper.lower.exponent",
    "logUpper.lower.mantissa",
    "logUpper.upper.exponent",
    "logUpper.upper.mantissa",
    "q.lower",
    "q.upper",
    "qPrime.lower",
    "qPrime.upper",
)

ROUNDED_LOG_COLUMNS = (
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


class EvaluationError(RuntimeError):
    """A malformed input or an exact-arithmetic compatibility failure."""


@dataclass(frozen=True, slots=True)
class Enclosure:
    lower: Fraction
    upper: Fraction


@dataclass(frozen=True, slots=True)
class LogRangeCertificate:
    exponent: int
    mantissa: Fraction


@dataclass(frozen=True, slots=True)
class LogIntervalCertificate:
    lower: LogRangeCertificate
    upper: LogRangeCertificate


@dataclass(frozen=True, slots=True)
class RoundedPointCertificate:
    sqrt_one_sub: Enclosure
    log_lower_probability: LogIntervalCertificate
    log_upper_probability: LogIntervalCertificate


@dataclass(frozen=True, slots=True)
class PointEvaluation:
    z: Fraction
    certificate: RoundedPointCertificate
    rounded_log_lower_probability: Enclosure
    rounded_log_upper_probability: Enclosure
    q: Enclosure
    q_prime: Enclosure

    def atomic_fields(self, cache_id: str) -> dict[str, str]:
        certificate = self.certificate
        return {
            "cacheId": cache_id,
            "z": lean_rational_repr(self.z),
            "sqrtOneSub.lower": lean_rational_repr(
                certificate.sqrt_one_sub.lower
            ),
            "sqrtOneSub.upper": lean_rational_repr(
                certificate.sqrt_one_sub.upper
            ),
            "sqrt.lower": lean_rational_repr(certificate.sqrt_one_sub.lower),
            "sqrt.upper": lean_rational_repr(certificate.sqrt_one_sub.upper),
            "logLower.lower.exponent": str(
                certificate.log_lower_probability.lower.exponent
            ),
            "logLower.lower.mantissa": lean_rational_repr(
                certificate.log_lower_probability.lower.mantissa
            ),
            "logLower.upper.exponent": str(
                certificate.log_lower_probability.upper.exponent
            ),
            "logLower.upper.mantissa": lean_rational_repr(
                certificate.log_lower_probability.upper.mantissa
            ),
            "logUpper.lower.exponent": str(
                certificate.log_upper_probability.lower.exponent
            ),
            "logUpper.lower.mantissa": lean_rational_repr(
                certificate.log_upper_probability.lower.mantissa
            ),
            "logUpper.upper.exponent": str(
                certificate.log_upper_probability.upper.exponent
            ),
            "logUpper.upper.mantissa": lean_rational_repr(
                certificate.log_upper_probability.upper.mantissa
            ),
            "logLowerEnclosure.lower": lean_rational_repr(
                self.rounded_log_lower_probability.lower
            ),
            "logLowerEnclosure.upper": lean_rational_repr(
                self.rounded_log_lower_probability.upper
            ),
            "logUpperEnclosure.lower": lean_rational_repr(
                self.rounded_log_upper_probability.lower
            ),
            "logUpperEnclosure.upper": lean_rational_repr(
                self.rounded_log_upper_probability.upper
            ),
            "q.lower": lean_rational_repr(self.q.lower),
            "q.upper": lean_rational_repr(self.q.upper),
            "qPrime.lower": lean_rational_repr(self.q_prime.lower),
            "qPrime.upper": lean_rational_repr(self.q_prime.upper),
        }


@dataclass(frozen=True, slots=True)
class ManifestPoint:
    cache_id: str
    z: Fraction


def fail(message: str) -> None:
    raise EvaluationError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return query_plan.canonical_json_bytes(value)


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
        fail(f"{context} is not a rational numerator/denominator pair")
    result = Fraction(value[0], value[1])
    if [result.numerator, result.denominator] != value:
        fail(f"{context} is not reduced with a positive denominator")
    return result


def parse_fraction(raw: str, context: str) -> Fraction:
    if re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", raw) is None:
        fail(f"{context} must be an integer or a canonical numerator/denominator")
    if "/" not in raw:
        return Fraction(int(raw))
    numerator, denominator = raw.split("/", 1)
    result = Fraction(int(numerator), int(denominator))
    canonical = str(result.numerator)
    if result.denominator != 1:
        canonical += f"/{result.denominator}"
    if canonical != raw:
        fail(f"{context} must be a reduced rational with positive denominator")
    return result


def lean_rational_repr(value: Fraction) -> str:
    """Match ``reprStr`` for Lean's canonical ``Rat`` values."""
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator} / {value.denominator}"


def point(value: Fraction) -> Enclosure:
    return Enclosure(value, value)


def add(left: Enclosure, right: Enclosure) -> Enclosure:
    return Enclosure(left.lower + right.lower, left.upper + right.upper)


def neg(value: Enclosure) -> Enclosure:
    return Enclosure(-value.upper, -value.lower)


def sub(left: Enclosure, right: Enclosure) -> Enclosure:
    return add(left, neg(right))


def center(value: Enclosure) -> Fraction:
    return (value.lower + value.upper) / 2


def radius(value: Enclosure) -> Fraction:
    return (value.upper - value.lower) / 2


def mul(left: Enclosure, right: Enclosure) -> Enclosure:
    """Port ``RationalEnclosure.mul`` (midpoint-radius, not corner hull)."""
    # Expanding Lean's midpoint-radius formula in the four possible center-sign
    # quadrants avoids constructing and normalizing its four half-endpoint
    # Fractions.  If ``w`` and ``v`` are the two interval widths, the extra
    # midpoint-radius slack is exactly ``w * v / 2``.
    left_nonnegative_center = left.lower + left.upper >= 0
    right_nonnegative_center = right.lower + right.upper >= 0
    excess = (left.upper - left.lower) * (right.upper - right.lower) / 2
    if left_nonnegative_center:
        if right_nonnegative_center:
            return Enclosure(
                left.lower * right.lower - excess,
                left.upper * right.upper,
            )
        return Enclosure(
            left.upper * right.lower,
            left.lower * right.upper + excess,
        )
    if right_nonnegative_center:
        return Enclosure(
            left.lower * right.upper,
            left.upper * right.lower + excess,
        )
    return Enclosure(
        left.upper * right.upper - excess,
        left.lower * right.lower,
    )


def scale(scalar: Fraction | int, value: Enclosure) -> Enclosure:
    # This is the exact specialization of ``mul (point scalar) value``; its
    # point radius is zero, so endpoint scaling is sufficient.
    scalar = Fraction(scalar)
    if scalar >= 0:
        return Enclosure(scalar * value.lower, scalar * value.upper)
    return Enclosure(scalar * value.upper, scalar * value.lower)


def inv_positive(value: Enclosure) -> Enclosure:
    if value.lower <= 0:
        fail("invPositive received an interval not bounded away from zero")
    return Enclosure(1 / value.upper, 1 / value.lower)


def div(left: Enclosure, right: Enclosure) -> Enclosure:
    return mul(left, inv_positive(right))


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil_fraction(value: Fraction) -> int:
    return -floor_fraction(-value)


def round_down(bits: int, value: Fraction) -> Fraction:
    if bits < 0:
        fail("dyadic precision must be nonnegative")
    dyadic_scale = 1 << bits
    scaled_floor = (value.numerator << bits) // value.denominator
    return Fraction(scaled_floor, dyadic_scale)


def round_up(bits: int, value: Fraction) -> Fraction:
    if bits < 0:
        fail("dyadic precision must be nonnegative")
    dyadic_scale = 1 << bits
    scaled_numerator = value.numerator << bits
    scaled_ceil = -((-scaled_numerator) // value.denominator)
    return Fraction(scaled_ceil, dyadic_scale)


def outer_enclosure(bits: int, value: Enclosure) -> Enclosure:
    return Enclosure(
        round_down(bits, value.lower), round_up(bits, value.upper)
    )


def sqrt_upper(y: Fraction) -> Fraction:
    y2 = y * y
    y3 = y2 * y
    y4 = y3 * y
    y5 = y4 * y
    y6 = y5 * y
    return (
        1
        - y / 2
        - y2 / 8
        - y3 / 16
        - 5 * y4 / 128
        - 7 * y5 / 256
        - 21 * y6 / 1024
    )


def sqrt_lower(y: Fraction) -> Fraction:
    return sqrt_upper(y) - y**7 / 32


def rounded_sqrt_certificate(bits: int, y: Fraction) -> Enclosure:
    upper = sqrt_upper(y)
    lower = upper - y**7 / 32
    return Enclosure(
        round_down(bits, lower), round_up(bits, upper)
    )


def auto_log_range_certificate(
    fuel: int, value: Fraction
) -> LogRangeCertificate:
    """Port the fuel-sensitive recursion without logarithms or floating point."""
    if fuel < 0:
        fail("log normalization fuel must be nonnegative")
    exponent = 0
    mantissa = value
    remaining = fuel
    while remaining > 0:
        if mantissa < 1:
            mantissa *= 2
            exponent -= 1
        elif mantissa < 2:
            return LogRangeCertificate(exponent, mantissa)
        else:
            mantissa /= 2
            exponent += 1
        remaining -= 1
    return LogRangeCertificate(exponent, mantissa)


def auto_log_interval_certificate(
    fuel: int, value: Enclosure
) -> LogIntervalCertificate:
    return LogIntervalCertificate(
        auto_log_range_certificate(fuel, value.lower),
        auto_log_range_certificate(fuel, value.upper),
    )


def log_ratio_coordinate(mantissa: Fraction) -> Fraction:
    return (mantissa - 1) / (mantissa + 1)


def atanh_partial(terms: int, coordinate: Fraction) -> Fraction:
    if terms < 0:
        fail("series term count must be nonnegative")
    coordinate_squared = coordinate * coordinate
    power = coordinate
    result = Fraction(0)
    for index in range(terms):
        result += power / (2 * index + 1)
        power *= coordinate_squared
    return result


def atanh_tail(terms: int, coordinate: Fraction) -> Fraction:
    coordinate_squared = coordinate * coordinate
    denominator = 1 - coordinate_squared
    if denominator == 0:
        fail("atanh tail denominator vanished")
    return coordinate ** (2 * terms + 1) / denominator


def half_log_ratio_enclosure(
    terms: int, coordinate: Fraction
) -> Enclosure:
    if terms < 0:
        fail("series term count must be nonnegative")
    if terms == 0:
        denominator = 1 - coordinate * coordinate
        if denominator == 0:
            fail("atanh tail denominator vanished")
        return Enclosure(Fraction(0), coordinate / denominator)

    # Put all ``terms`` summands over one integer common denominator and reduce
    # only the final Fraction.  Repeated Fraction addition spends most of the
    # exact evaluator's time normalizing the same powers of the coordinate's
    # denominator.  This is algebraically the same finite series as
    # ``atanh_partial`` above.
    numerator = coordinate.numerator
    denominator = coordinate.denominator
    maximum_power = 2 * terms - 1
    denominator_power = denominator**maximum_power
    common_odd_denominator = odd_denominator_lcm(terms)
    partial_numerator = sum(
        numerator ** (2 * index + 1)
        * denominator ** (maximum_power - (2 * index + 1))
        * (common_odd_denominator // (2 * index + 1))
        for index in range(terms)
    )
    partial = Fraction(
        partial_numerator, denominator_power * common_odd_denominator
    )
    tail_denominator = denominator_power * (
        denominator * denominator - numerator * numerator
    )
    if tail_denominator == 0:
        fail("atanh tail denominator vanished")
    tail = Fraction(numerator ** (2 * terms + 1), tail_denominator)
    return Enclosure(partial, partial + tail)


@lru_cache(maxsize=128)
def odd_denominator_lcm(terms: int) -> int:
    """LCM of the odd denominators in an ``atanh`` partial sum."""
    return math.lcm(*(2 * index + 1 for index in range(terms)))


def log_mantissa_enclosure(terms: int, mantissa: Fraction) -> Enclosure:
    return scale(
        2, half_log_ratio_enclosure(terms, log_ratio_coordinate(mantissa))
    )


@lru_cache(maxsize=16)
def log_two_enclosure(terms: int) -> Enclosure:
    return log_mantissa_enclosure(terms, Fraction(2))


def log_range_enclosure(
    terms: int,
    certificate: LogRangeCertificate,
    cached_log_two: Enclosure | None = None,
) -> Enclosure:
    log_two = cached_log_two if cached_log_two is not None else log_two_enclosure(terms)
    return add(
        scale(certificate.exponent, log_two),
        log_mantissa_enclosure(terms, certificate.mantissa),
    )


def log_interval_enclosure(
    terms: int,
    certificate: LogIntervalCertificate,
    cached_log_two: Enclosure | None = None,
) -> Enclosure:
    lower = log_range_enclosure(terms, certificate.lower, cached_log_two)
    upper = log_range_enclosure(terms, certificate.upper, cached_log_two)
    return Enclosure(lower.lower, upper.upper)


def lower_probability(sqrt_enclosure: Enclosure) -> Enclosure:
    return Enclosure(
        (1 - sqrt_enclosure.upper) / 2,
        (1 - sqrt_enclosure.lower) / 2,
    )


def upper_probability(sqrt_enclosure: Enclosure) -> Enclosure:
    return Enclosure(
        (1 + sqrt_enclosure.lower) / 2,
        (1 + sqrt_enclosure.upper) / 2,
    )


def rounded_auto_certificate(
    sqrt_bits: int, log_fuel: int, z: Fraction
) -> RoundedPointCertificate:
    sqrt_one_sub = rounded_sqrt_certificate(sqrt_bits, z)
    lower = lower_probability(sqrt_one_sub)
    upper = upper_probability(sqrt_one_sub)
    return RoundedPointCertificate(
        sqrt_one_sub,
        auto_log_interval_certificate(log_fuel, lower),
        auto_log_interval_certificate(log_fuel, upper),
    )


def certificate_enclosure(
    terms: int, certificate: RoundedPointCertificate
) -> Enclosure:
    cached_log_two = log_two_enclosure(terms)
    lower = lower_probability(certificate.sqrt_one_sub)
    upper = upper_probability(certificate.sqrt_one_sub)
    lower_log = log_interval_enclosure(
        terms, certificate.log_lower_probability, cached_log_two
    )
    upper_log = log_interval_enclosure(
        terms, certificate.log_upper_probability, cached_log_two
    )
    return neg(add(mul(lower, lower_log), mul(upper, upper_log)))


def certificate_enclosure_from_logs(
    certificate: RoundedPointCertificate,
    lower_log: Enclosure,
    upper_log: Enclosure,
) -> Enclosure:
    lower = lower_probability(certificate.sqrt_one_sub)
    upper = upper_probability(certificate.sqrt_one_sub)
    return neg(add(mul(lower, lower_log), mul(upper, upper_log)))


def certificate_prime_enclosure(
    terms: int, certificate: RoundedPointCertificate
) -> Enclosure:
    cached_log_two = log_two_enclosure(terms)
    lower_log = log_interval_enclosure(
        terms, certificate.log_lower_probability, cached_log_two
    )
    upper_log = log_interval_enclosure(
        terms, certificate.log_upper_probability, cached_log_two
    )
    return scale(
        Fraction(1, 4),
        div(sub(upper_log, lower_log), certificate.sqrt_one_sub),
    )


def certificate_prime_enclosure_from_logs(
    certificate: RoundedPointCertificate,
    lower_log: Enclosure,
    upper_log: Enclosure,
) -> Enclosure:
    return scale(
        Fraction(1, 4),
        div(sub(upper_log, lower_log), certificate.sqrt_one_sub),
    )


def certificate_succeeds(
    z: Fraction, certificate: RoundedPointCertificate
) -> bool:
    sqrt_value = certificate.sqrt_one_sub
    sqrt_input = 1 - z
    sqrt_ok = (
        0 <= sqrt_input
        and 0 <= sqrt_value.lower
        and sqrt_value.lower**2 <= sqrt_input
        and 0 <= sqrt_value.upper
        and sqrt_input <= sqrt_value.upper**2
        and 0 < sqrt_value.lower
    )
    lower = lower_probability(sqrt_value)
    upper = upper_probability(sqrt_value)

    def range_ok(value: Fraction, range_certificate: LogRangeCertificate) -> bool:
        if range_certificate.exponent >= 0:
            power = Fraction(1 << range_certificate.exponent)
        else:
            power = Fraction(1, 1 << -range_certificate.exponent)
        return (
            1 <= range_certificate.mantissa < 2
            and value == power * range_certificate.mantissa
        )

    logs_ok = (
        lower.lower > 0
        and range_ok(lower.lower, certificate.log_lower_probability.lower)
        and range_ok(lower.upper, certificate.log_lower_probability.upper)
        and upper.lower > 0
        and range_ok(upper.lower, certificate.log_upper_probability.lower)
        and range_ok(upper.upper, certificate.log_upper_probability.upper)
    )
    return sqrt_ok and logs_ok


def evaluate_point(
    z: Fraction,
    *,
    point_bits: int = 40,
    terms: int = 12,
    sqrt_bits: int = 40,
    log_fuel: int = 48,
) -> PointEvaluation:
    if point_bits < 0 or sqrt_bits < 0 or terms < 0 or log_fuel < 0:
        fail("evaluation parameters must be nonnegative")
    certificate = rounded_auto_certificate(sqrt_bits, log_fuel, z)
    if not certificate_succeeds(z, certificate):
        fail(f"rounded point certificate did not validate at z={z}")
    cached_log_two = log_two_enclosure(terms)
    lower_log = log_interval_enclosure(
        terms, certificate.log_lower_probability, cached_log_two
    )
    upper_log = log_interval_enclosure(
        terms, certificate.log_upper_probability, cached_log_two
    )
    rounded_lower_log = outer_enclosure(point_bits, lower_log)
    rounded_upper_log = outer_enclosure(point_bits, upper_log)
    # The production cached-log evaluator deliberately uses the small dyadic
    # log outers in both scalar formulas.  This ports
    # LRUpperKCachedLogPointCertificate.rawValues followed by outerValues.
    q = outer_enclosure(
        point_bits,
        certificate_enclosure_from_logs(
            certificate, rounded_lower_log, rounded_upper_log
        ),
    )
    q_prime = outer_enclosure(
        point_bits,
        certificate_prime_enclosure_from_logs(
            certificate, rounded_lower_log, rounded_upper_log
        ),
    )
    if q.lower > q.upper or q_prime.lower > q_prime.upper:
        fail(f"computed a reversed point interval at z={z}")
    return PointEvaluation(
        z, certificate, rounded_lower_log, rounded_upper_log, q, q_prime
    )


def render_row(
    cache_id: str, evaluation: PointEvaluation, columns: tuple[str, ...]
) -> bytes:
    if columns not in (
        ORIGINAL_COLUMNS,
        FULL_CERTIFICATE_COLUMNS,
        ROUNDED_LOG_COLUMNS,
    ):
        fail("unsupported fast-point query column schema")
    fields = evaluation.atomic_fields(cache_id)
    return ("\t".join(fields[column] for column in columns) + "\n").encode(
        "ascii"
    )


def self_check() -> None:
    """Small independent identities guarding the port's delicate semantics."""
    def reference_mul(left: Enclosure, right: Enclosure) -> Enclosure:
        left_center = center(left)
        right_center = center(right)
        left_radius = radius(left)
        right_radius = radius(right)
        product_center = left_center * right_center
        product_radius = (
            abs(left_center) * right_radius
            + abs(right_center) * left_radius
            + left_radius * right_radius
        )
        return Enclosure(
            product_center - product_radius,
            product_center + product_radius,
        )

    sign_quadrant_intervals = (
        (
            Enclosure(Fraction(1, 3), Fraction(5, 4)),
            Enclosure(Fraction(2), Fraction(3)),
        ),
        (
            Enclosure(Fraction(1, 3), Fraction(5, 4)),
            Enclosure(Fraction(-3), Fraction(-2)),
        ),
        (
            Enclosure(Fraction(-5, 4), Fraction(-1, 3)),
            Enclosure(Fraction(2), Fraction(3)),
        ),
        (
            Enclosure(Fraction(-5, 4), Fraction(-1, 3)),
            Enclosure(Fraction(-3), Fraction(-2)),
        ),
        (
            Enclosure(Fraction(-1), Fraction(1)),
            Enclosure(Fraction(-2, 3), Fraction(5, 3)),
        ),
    )
    for left, right in sign_quadrant_intervals:
        if mul(left, right) != reference_mul(left, right):
            fail("expanded midpoint-radius multiplication identity failed")
    scale_sample = Enclosure(Fraction(-2, 5), Fraction(7, 6))
    for scalar in (Fraction(-3, 2), Fraction(0), Fraction(5, 4)):
        if scale(scalar, scale_sample) != reference_mul(point(scalar), scale_sample):
            fail("point-radius scaling specialization failed")
    probability_sample = Enclosure(Fraction(1, 5), Fraction(2, 3))
    if lower_probability(probability_sample) != reference_mul(
        point(Fraction(1, 2)), sub(point(Fraction(1)), probability_sample)
    ):
        fail("lower-probability endpoint specialization failed")
    if upper_probability(probability_sample) != reference_mul(
        point(Fraction(1, 2)), add(point(Fraction(1)), probability_sample)
    ):
        fail("upper-probability endpoint specialization failed")
    for terms, coordinate in (
        (0, Fraction(1, 3)),
        (1, Fraction(2, 7)),
        (4, Fraction(-3, 11)),
        (12, Fraction(17, 53)),
    ):
        partial = atanh_partial(terms, coordinate)
        expected = Enclosure(partial, partial + atanh_tail(terms, coordinate))
        if half_log_ratio_enclosure(terms, coordinate) != expected:
            fail("common-denominator atanh series identity failed")
    if round_down(3, Fraction(-1, 10)) != Fraction(-1, 8):
        fail("signed roundDown compatibility check failed")
    if round_up(3, Fraction(-1, 10)) != Fraction(0):
        fail("signed roundUp compatibility check failed")
    if auto_log_range_certificate(48, Fraction(3, 8)) != LogRangeCertificate(
        -2, Fraction(3, 2)
    ):
        fail("lower dyadic range-reduction check failed")
    if auto_log_range_certificate(48, Fraction(5)) != LogRangeCertificate(
        2, Fraction(5, 4)
    ):
        fail("upper dyadic range-reduction check failed")
    # The zero-fuel case is intentionally not normalized in Lean.
    if auto_log_range_certificate(0, Fraction(3, 8)) != LogRangeCertificate(
        0, Fraction(3, 8)
    ):
        fail("zero-fuel range-reduction semantics drifted")
    sample = evaluate_point(Fraction(1, 4096))
    if sample.certificate.sqrt_one_sub.lower.denominator > 1 << 40:
        fail("rounded square-root lower endpoint is not a 40-bit dyadic")
    if sample.certificate.sqrt_one_sub.upper.denominator > 1 << 40:
        fail("rounded square-root upper endpoint is not a 40-bit dyadic")
    if sample.q.lower.denominator > 1 << 40 or sample.q.upper.denominator > 1 << 40:
        fail("rounded Q endpoints are not 40-bit dyadics")
    if (
        sample.q_prime.lower.denominator > 1 << 40
        or sample.q_prime.upper.denominator > 1 << 40
    ):
        fail("rounded Q' endpoints are not 40-bit dyadics")
    # Saved ordinary-Lean #eval fixture for the first authenticated point.
    # This compares the delicate Rat floor/ceil, recursive range reduction,
    # midpoint-radius interval arithmetic, series, and outer rounding at once.
    lean_fixture_point = Fraction(549153, 549755813888)
    fixture = evaluate_point(lean_fixture_point)
    raw_log_two = log_two_enclosure(12)
    raw_lower_log = log_interval_enclosure(
        12, fixture.certificate.log_lower_probability, raw_log_two
    )
    raw_upper_log = log_interval_enclosure(
        12, fixture.certificate.log_upper_probability, raw_log_two
    )
    raw_q = outer_enclosure(
        40,
        certificate_enclosure_from_logs(
            fixture.certificate, raw_lower_log, raw_upper_log
        ),
    )
    raw_q_prime = outer_enclosure(
        40,
        certificate_prime_enclosure_from_logs(
            fixture.certificate, raw_lower_log, raw_upper_log
        ),
    )
    observed = (
        fixture.certificate.sqrt_one_sub.lower,
        fixture.certificate.sqrt_one_sub.upper,
        fixture.certificate.log_lower_probability.lower.exponent,
        fixture.certificate.log_lower_probability.lower.mantissa,
        fixture.certificate.log_lower_probability.upper.exponent,
        fixture.certificate.log_lower_probability.upper.mantissa,
        fixture.certificate.log_upper_probability.lower.exponent,
        fixture.certificate.log_upper_probability.lower.mantissa,
        fixture.certificate.log_upper_probability.upper.exponent,
        fixture.certificate.log_upper_probability.upper.mantissa,
        raw_q.lower,
        raw_q.upper,
        raw_q_prime.lower,
        raw_q_prime.upper,
    )
    expected = (
        Fraction(549755539311, 549755813888),
        Fraction(1099511078623, 1099511627776),
        -22,
        Fraction(549153, 524288),
        -22,
        Fraction(274577, 262144),
        -1,
        Fraction(1099511353199, 549755813888),
        -1,
        Fraction(2199022706399, 1099511627776),
        Fraction(1112233, 274877906944),
        Fraction(1112237, 274877906944),
        Fraction(1044735852057, 274877906944),
        Fraction(4178943908799, 1099511627776),
    )
    if observed != expected:
        fail("exact evaluator disagrees with the saved Lean point fixture")


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


def read_manifest(path: Path, query_dir: Path) -> dict[str, Any]:
    if path.parent != query_dir:
        fail("--query-manifest must be directly inside --query-dir")
    data = query_plan.replay.read_regular_file(
        path, "fast point query manifest", MAX_MANIFEST_BYTES
    )
    try:
        manifest = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot parse fast point query manifest: {error}")
    if not isinstance(manifest, dict):
        fail("fast point query manifest must be a JSON object")
    plan_sha = manifest.get("planSha256")
    if not isinstance(plan_sha, str) or HEX64_PATTERN.fullmatch(plan_sha) is None:
        fail("fast point query manifest has an invalid planSha256")
    core = dict(manifest)
    del core["planSha256"]
    if sha256_bytes(canonical_json_bytes(core)) != plan_sha:
        fail("fast point query manifest planSha256 does not authenticate its content")
    if manifest.get("format") != query_plan.FORMAT:
        fail("fast point query manifest format drifted")
    if manifest.get("proofAuthority") != query_plan.PROOF_AUTHORITY:
        fail("fast point query proof-authority declaration drifted")
    if manifest.get("outputDirectory") != query_plan.replay.relative_project_path(
        query_dir
    ):
        fail("query manifest outputDirectory differs from --query-dir")
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
        fail("query manifest is not bound to the current generators")
    expected_implementation = {
        "directReplay": query_plan.replay.bind_direct_replay_sources(),
        "fastPointCache": query_plan.bind_fast_point_sources(),
    }
    if manifest.get("implementation") != expected_implementation:
        fail("query manifest is not bound to the current fast-point implementation")
    return manifest


def strict_int(value: object, context: str, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
        fail(f"{context} is not an integer at least {minimum}")
    return value


def manifest_modules(
    manifest: dict[str, Any], query_dir: Path
) -> tuple[dict[str, int | str], tuple[str, ...], list[tuple[str, list[ManifestPoint]]]]:
    parameters = manifest.get("parameters")
    if not isinstance(parameters, dict):
        fail("fast point query parameters are malformed")
    if parameters.get("cacheKeySchema") != query_plan.CACHE_KEY_SCHEMA:
        fail("fast point cache-key schema drifted")
    if parameters.get("certificateScheme") != query_plan.FAST_CERTIFICATE_SCHEME:
        fail("fast point certificate scheme drifted")
    point_bits = strict_int(parameters.get("pointDyadicBits"), "pointDyadicBits")
    log_bits = strict_int(parameters.get("logDyadicBits"), "logDyadicBits")
    sqrt_bits = strict_int(parameters.get("sqrtDyadicBits"), "sqrtDyadicBits")
    terms = strict_int(parameters.get("terms"), "terms")
    log_fuel = strict_int(parameters.get("logFuel"), "logFuel")
    if (
        point_bits > 256
        or log_bits > 256
        or sqrt_bits > 256
        or terms > 128
        or log_fuel > 256
    ):
        fail("fast point parameters exceed the evaluator's hard guards")
    if log_bits != point_bits:
        fail("the cached-log evaluator currently requires logDyadicBits = pointDyadicBits")
    prefix = parameters.get("modulePrefix")
    if not isinstance(prefix, str):
        fail("fast point modulePrefix is not a string")
    query_plan.query_module_prefix(prefix)

    query_output = manifest.get("queryOutput")
    if not isinstance(query_output, dict):
        fail("fast point queryOutput schema is malformed")
    if query_output.get("schema") != query_plan.QUERY_ROW_SCHEMA:
        fail("fast point query row-schema identity drifted")
    raw_columns = query_output.get("columns")
    if not isinstance(raw_columns, list) or not all(
        isinstance(column, str) for column in raw_columns
    ):
        fail("fast point query columns are malformed")
    columns = tuple(raw_columns)
    if columns not in (
        ORIGINAL_COLUMNS,
        FULL_CERTIFICATE_COLUMNS,
        ROUNDED_LOG_COLUMNS,
    ):
        fail("fast point query columns are not a supported exact evaluator schema")
    if query_output.get("columnCount") != len(columns):
        fail("fast point query columnCount disagrees with its columns")

    selected = manifest.get("selected")
    queries = manifest.get("queries")
    outputs = manifest.get("outputs")
    if (
        not isinstance(selected, list)
        or not isinstance(queries, list)
        or not isinstance(outputs, dict)
    ):
        fail("fast point query addressing tables are malformed")
    if len(selected) != manifest.get("selectedPointKeys"):
        fail("fast point selected table has the wrong length")
    if len(queries) != manifest.get("queryModuleCount"):
        fail("fast point query table has the wrong length")

    key_args = argparse.Namespace(
        dyadic_bits=point_bits,
        point_sqrt_bits=sqrt_bits,
        terms=terms,
        authenticated_log_fuel=log_fuel,
    )
    by_module: dict[str, list[tuple[int, ManifestPoint]]] = {}
    seen_ids: set[str] = set()
    seen_points: set[Fraction] = set()
    for ordinal, record in enumerate(selected):
        if not isinstance(record, dict):
            fail(f"selected[{ordinal}] is not an object")
        identifier = record.get("cacheId")
        module = record.get("queryModule")
        index = strict_int(record.get("queryIndex"), f"selected[{ordinal}].queryIndex")
        if (
            not isinstance(identifier, str)
            or HEX64_PATTERN.fullmatch(identifier) is None
            or not isinstance(module, str)
        ):
            fail(f"selected[{ordinal}] has invalid query addressing")
        z = fraction_from_record(record.get("z"), f"selected[{ordinal}].z")
        if not Fraction(0) < z <= Fraction(1, 16):
            fail(f"selected[{ordinal}].z escaped (0,1/16]")
        if query_plan.cache_id(z, key_args) != identifier:
            fail(f"selected[{ordinal}] cache ID does not hash its exact key")
        if identifier in seen_ids or z in seen_points:
            fail("fast point selected table repeats an ID or rational point")
        seen_ids.add(identifier)
        seen_points.add(z)
        by_module.setdefault(module, []).append((index, ManifestPoint(identifier, z)))

    result: list[tuple[str, list[ManifestPoint]]] = []
    flattened = 0
    for ordinal, query in enumerate(queries):
        if not isinstance(query, dict):
            fail(f"queries[{ordinal}] is not an object")
        module = query.get("module")
        if module != f"{prefix}Q{ordinal:04d}":
            fail(f"query module order drifted at ordinal {ordinal}")
        count = strict_int(query.get("queryCount"), f"queries[{ordinal}].queryCount", 1)
        entries = sorted(by_module.get(module, []), key=lambda entry: entry[0])
        if [index for index, _point in entries] != list(range(count)):
            fail(f"query indexes are not contiguous for {module}")
        points = [entry for _index, entry in entries]
        if (
            not points
            or query.get("firstCacheId") != points[0].cache_id
            or query.get("lastCacheId") != points[-1].cache_id
        ):
            fail(f"query cache-ID endpoints drifted for {module}")
        filename = f"{module}.lean"
        expected_sha = outputs.get(filename)
        if not isinstance(expected_sha, str) or HEX64_PATTERN.fullmatch(expected_sha) is None:
            fail(f"query output hash is missing for {filename}")
        source = query_dir / filename
        source_bytes = query_plan.replay.read_regular_file(
            source, f"fast point query source {filename}", MAX_SOURCE_BYTES
        )
        if sha256_bytes(source_bytes) != expected_sha:
            fail(f"fast point query source hash drifted for {filename}")
        result.append((module, points))
        flattened += len(points)
    if flattened != len(selected) or set(by_module) != {module for module, _ in result}:
        fail("fast point selected rows and query modules disagree")
    return (
        {
            "pointBits": point_bits,
            "logBits": log_bits,
            "sqrtBits": sqrt_bits,
            "terms": terms,
            "logFuel": log_fuel,
            "prefix": prefix,
        },
        columns,
        result,
    )


def exclusive_write(
    path: Path, data: bytes, output_identity: tuple[int, int]
) -> None:
    if len(data) > MAX_OUTPUT_BYTES:
        fail(f"refusing output larger than {MAX_OUTPUT_BYTES} bytes: {path.name}")
    query_plan.replay.exclusive_create_all(
        path.parent, output_identity, {path: data}
    )


def command_point(args: argparse.Namespace) -> None:
    self_check()
    z = parse_fraction(args.z, "z")
    evaluation = evaluate_point(
        z,
        point_bits=args.point_bits,
        terms=args.terms,
        sqrt_bits=args.sqrt_bits,
        log_fuel=args.log_fuel,
    )
    cache_id = args.cache_id or "point"
    if args.schema == "original":
        columns = ORIGINAL_COLUMNS
    elif args.schema == "certificate":
        columns = FULL_CERTIFICATE_COLUMNS
    else:
        columns = ROUNDED_LOG_COLUMNS
    sys.stdout.buffer.write(render_row(cache_id, evaluation, columns))


def command_evaluate_manifest(args: argparse.Namespace) -> None:
    if not args.confirm_write:
        fail("refusing manifest evaluation without --confirm-write")
    if args.max_modules < 1:
        fail("--max-modules must be positive")
    self_check()
    query_plan.replay.validate_repository_location()
    query_dir, _query_identity = scratch_directory(args.query_dir, "--query-dir")
    output_dir, output_identity = scratch_directory(args.output_dir, "--output-dir")
    manifest_path = query_plan.replay.project_path(
        args.query_manifest, "--query-manifest"
    )
    manifest = read_manifest(manifest_path, query_dir)
    parameters, columns, modules = manifest_modules(manifest, query_dir)
    output_metadata = output_dir.stat()
    if (output_metadata.st_dev, output_metadata.st_ino) != output_identity:
        fail("--output-dir identity changed before evaluation")

    processed = 0
    reused = 0
    started = time.monotonic()
    for ordinal, (module, points) in enumerate(modules):
        output_path = query_plan.replay.safe_output_path(
            output_dir, f"{module}.out"
        )
        exists = output_path.exists() or output_path.is_symlink()
        if not exists and processed >= args.max_modules:
            continue
        module_started = time.monotonic()
        rows = []
        for manifest_point in points:
            value = evaluate_point(
                manifest_point.z,
                point_bits=int(parameters["pointBits"]),
                terms=int(parameters["terms"]),
                sqrt_bits=int(parameters["sqrtBits"]),
                log_fuel=int(parameters["logFuel"]),
            )
            rows.append(render_row(manifest_point.cache_id, value, columns))
        data = b"".join(rows)
        if exists:
            existing = query_plan.replay.read_regular_file(
                output_path, f"existing exact point output {output_path.name}", MAX_OUTPUT_BYTES
            )
            if existing != data:
                fail(f"existing output differs from exact evaluation: {output_path.name}")
            reused += 1
        else:
            exclusive_write(output_path, data, output_identity)
            processed += 1
        print(
            json.dumps(
                {
                    "status": "reused" if exists else "written",
                    "module": module,
                    "ordinal": ordinal,
                    "queries": len(points),
                    "seconds": round(time.monotonic() - module_started, 3),
                },
                sort_keys=True,
            ),
            flush=True,
        )

    completed = 0
    for module, _points in modules:
        candidate = query_plan.replay.safe_output_path(output_dir, f"{module}.out")
        if candidate.exists() and not candidate.is_symlink():
            completed += 1
    print(
        json.dumps(
            {
                "status": "complete" if completed == len(modules) else "partial",
                "moduleCount": len(modules),
                "newModules": processed,
                "completedModules": completed,
                "reusedModules": reused,
                "remainingModules": len(modules) - completed,
                "elapsedSeconds": round(time.monotonic() - started, 3),
                "evaluator": {
                    "file": SCRIPT.name,
                    "byteSha256": SCRIPT_BYTE_SHA256,
                    "proofAuthority": "none",
                },
            },
            sort_keys=True,
        ),
        flush=True,
    )


def command_self_check(_args: argparse.Namespace) -> None:
    self_check()
    print(json.dumps({"status": "ok", "evaluatorSha256": SCRIPT_BYTE_SHA256}))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)

    point_command = commands.add_parser("point", help="evaluate one rational point")
    point_command.add_argument("z")
    point_command.add_argument("--cache-id")
    point_command.add_argument("--point-bits", type=int, default=40)
    point_command.add_argument("--sqrt-bits", type=int, default=40)
    point_command.add_argument("--terms", type=int, default=12)
    point_command.add_argument("--log-fuel", type=int, default=48)
    point_command.add_argument(
        "--schema",
        choices=("original", "certificate", "rounded-logs"),
        default="rounded-logs",
    )
    point_command.set_defaults(handler=command_point)

    manifest_command = commands.add_parser(
        "evaluate-manifest",
        help="fill query-module outputs with exact Fraction evaluation",
    )
    manifest_command.add_argument("--query-dir", required=True)
    manifest_command.add_argument("--query-manifest", required=True)
    manifest_command.add_argument("--output-dir", required=True)
    manifest_command.add_argument("--max-modules", type=int, default=20_000)
    manifest_command.add_argument("--confirm-write", action="store_true")
    manifest_command.set_defaults(handler=command_evaluate_manifest)

    check_command = commands.add_parser(
        "self-check", help="run exact arithmetic regression checks"
    )
    check_command.set_defaults(handler=command_self_check)
    return result


def main(argv: Iterable[str] | None = None) -> None:
    args = parser().parse_args(list(argv) if argv is not None else None)
    args.handler(args)


if __name__ == "__main__":
    try:
        main()
    except (EvaluationError, query_plan.replay.ReplayPlanError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
