#!/usr/bin/env python3
"""Generate the fixed eight-strip centered monotone certificate plan.

This is an untrusted, deterministic data generator.  It uses only exact
``Fraction`` and integer arithmetic and independently mirrors the executable
fixed-dyadic recurrence in
``LRCompactVCenteredMonotoneEvalCore``.  The generated observations are still
intended to be checked by ordinary Lean kernel reduction.

There is deliberately no topology search here.  The eight rows, their heads,
and the two tangent centers are a fixed audited design.  The script rebuilds:

* the common 96-bit outward ``R`` and exact ``x`` inputs;
* the sharp ``W_R(1)`` input (256-term positive lower head and the existing
  34-term, ``J=72`` Abel endpoint upper construction);
* each exact same-``y`` logarithm range certificate and dyadic lambda;
* both exact same-``y`` budget predicates; and
* the fused corner/tangent observations and final lower numerator.

The compact JSON plan stores common data once and only fixed-dyadic endpoint
numerators in row payloads.  It contains no proof authority.  The segmented
Lean renderer emits a proof-free configuration module, four independently
kernel-checked two-leaf arithmetic chunks, an arithmetic-free checked-tree
assembly, and a one-import semantic endpoint.  Thus a failed replay never
forces the other six leaves to be recomputed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable


sys.dont_write_bytecode = True


class GenerationError(RuntimeError):
    """A fixed design invariant or exact certificate check failed."""


def fail(message: str) -> None:
    raise GenerationError(message)


SCRIPT = Path(__file__).resolve()
BITS = 96
SCALE = 1 << BITS
LOG_TERMS = 34
HALF_LOG_TERMS = 34
D_TERMS = 34
LOG_FUEL = 16
W_LOWER_TERMS = 256
W_ABEL_TERMS = 34
W_ABEL_J = 72
R_LO = Fraction(921, 1024)
R_HI = Fraction(9, 10)
X_LO = Fraction(63, 64)
X_HI = Fraction(127, 128)
LAMBDA_GUARD_UNITS = 4

MAX_ROWS = 8
MAX_HEAD = 192
EXPECTED_WEIGHTED_HEADS = 1152
MAX_OUTPUT_BYTES = 128 * 1024
MAX_SEGMENTED_OUTPUT_BYTES = 512 * 1024
MAX_FRACTION_BITS = 262_144
DEFAULT_CHUNK_SIZE = 2
ALLOWED_CHUNK_SIZES = (2,)

LEAN_NAMESPACE = "GeneratedLRCompactVCenteredMonotoneV1"
LEAN_MODULE_PREFIX = (
    "InformationTheory.CourtadeKumar."
    "GeneratedLRCompactVCenteredMonotoneV1"
)

# Boundary indices in the fixed ROWS sequence.  A split at index i uses the
# common boundary ROWS[i].v_lo and leaves [0, i) below it.  This is the exact
# balanced topology audited for the eight adjacent strips.
ROOT_SPLIT_INDEX = 4
LEFT_SPLIT_INDEX = 2
LEFT_LEFT_SPLIT_INDEX = 1
LEFT_RIGHT_SPLIT_INDEX = 3
RIGHT_SPLIT_INDEX = 6
RIGHT_LEFT_SPLIT_INDEX = 5
RIGHT_RIGHT_SPLIT_INDEX = 7

LEAN_FORBIDDEN_TOKENS = (
    "native_decide",
    "vm_decide",
    "ofReduceBool",
    "trustCompiler",
    "run_tac",
    "sorry",
    "admit",
)

EXPECTED_W_LOWER_NUMERATOR = 1782141680280723889127714657
EXPECTED_W_UPPER_NUMERATOR = 1869861642996119020795856175
EXPECTED_DESIGN_SHA256 = (
    "5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325"
)
EXPECTED_OBSERVATION_SHA256 = (
    "43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421"
)
EXPECTED_LAMBDA_NUMERATORS = (
    13834888887324821975059747083,
    14960625174002381896681370548,
    15951159665030050164768612277,
    16689861455500656831882410258,
    17511123416826155740579640948,
    18442945384415776252697960556,
    18946394230310079465403036085,
    19482793518227463114124536054,
)


@dataclass(frozen=True, slots=True)
class RowSpec:
    v_lo: Fraction
    v_hi: Fraction
    head: int
    mode: str
    x_point: Fraction


ROWS = (
    RowSpec(Fraction(480, 512), Fraction(484, 512), 192,
            "tangent", Fraction(253, 256)),
    RowSpec(Fraction(484, 512), Fraction(487, 512), 128,
            "tangent", Fraction(127, 128)),
    RowSpec(Fraction(487, 512), Fraction(489, 512), 128,
            "corner", X_HI),
    RowSpec(Fraction(489, 512), Fraction(491, 512), 128,
            "corner", X_HI),
    RowSpec(Fraction(491, 512), Fraction(493, 512), 192,
            "corner", X_HI),
    RowSpec(Fraction(493, 512), Fraction(494, 512), 128,
            "corner", X_HI),
    RowSpec(Fraction(494, 512), Fraction(495, 512), 128,
            "corner", X_HI),
    RowSpec(Fraction(495, 512), Fraction(496, 512), 128,
            "corner", X_HI),
)


@dataclass(frozen=True, slots=True)
class RatInterval:
    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        if self.lower > self.upper:
            fail("inverted exact rational interval")


@dataclass(frozen=True, slots=True)
class LogRange:
    exponent: int
    mantissa: Fraction


@dataclass(frozen=True, slots=True)
class NatInterval:
    lower: int
    upper: int

    def __post_init__(self) -> None:
        if self.lower < 0 or self.lower > self.upper:
            fail("invalid nonnegative fixed-dyadic interval")


@dataclass(frozen=True, slots=True)
class IntInterval:
    lower: int
    upper: int

    def __post_init__(self) -> None:
        if self.lower > self.upper:
            fail("inverted signed fixed-dyadic interval")


@dataclass(frozen=True, slots=True)
class ScoreEndpointState:
    score: NatInterval
    increment_base: NatInterval


@dataclass(frozen=True, slots=True)
class XPowerState:
    previous_previous: NatInterval
    previous: NatInterval
    current: NatInterval


@dataclass(frozen=True, slots=True)
class VPowerState:
    even: NatInterval
    odd: NatInterval


@dataclass(frozen=True, slots=True)
class FixedOutput:
    p: IntInterval
    pv: IntInterval
    px: IntInterval
    pxx: IntInterval


def fraction_guard(value: Fraction, context: str) -> None:
    if (value.numerator.bit_length() > MAX_FRACTION_BITS
            or value.denominator.bit_length() > MAX_FRACTION_BITS):
        fail(f"{context}: exact fraction exceeded resource bit guard")


def rat_add(left: RatInterval, right: RatInterval) -> RatInterval:
    return RatInterval(left.lower + right.lower, left.upper + right.upper)


def rat_neg(value: RatInterval) -> RatInterval:
    return RatInterval(-value.upper, -value.lower)


def rat_sub(left: RatInterval, right: RatInterval) -> RatInterval:
    return rat_add(left, rat_neg(right))


def rat_center(value: RatInterval) -> Fraction:
    return (value.lower + value.upper) / 2


def rat_radius(value: RatInterval) -> Fraction:
    return (value.upper - value.lower) / 2


def rat_mul(left: RatInterval, right: RatInterval) -> RatInterval:
    """Mirror ``RationalEnclosure.mul`` midpoint-radius arithmetic."""
    center = rat_center(left) * rat_center(right)
    radius = (
        abs(rat_center(left)) * rat_radius(right)
        + abs(rat_center(right)) * rat_radius(left)
        + rat_radius(left) * rat_radius(right)
    )
    return RatInterval(center - radius, center + radius)


def rat_scale(coefficient: Fraction | int,
              value: RatInterval) -> RatInterval:
    return rat_mul(RatInterval(Fraction(coefficient), Fraction(coefficient)),
                   value)


def atanh_enclosure(terms: int, coordinate: Fraction) -> RatInterval:
    if terms < 0 or not 0 <= coordinate < 1:
        fail("atanh enclosure coordinate outside [0,1)")
    partial = sum(
        (coordinate ** (2 * index + 1) / (2 * index + 1)
         for index in range(terms)),
        Fraction(0),
    )
    tail = coordinate ** (2 * terms + 1) / (1 - coordinate * coordinate)
    result = RatInterval(partial, partial + tail)
    fraction_guard(result.upper, "atanh enclosure")
    return result


def log_mantissa_enclosure(terms: int, mantissa: Fraction) -> RatInterval:
    if not 1 <= mantissa <= 2:
        fail("log mantissa outside [1,2]")
    coordinate = (mantissa - 1) / (mantissa + 1)
    return rat_scale(2, atanh_enclosure(terms, coordinate))


def log_two_enclosure(terms: int) -> RatInterval:
    return log_mantissa_enclosure(terms, Fraction(2))


def auto_log_range(fuel: int, value: Fraction) -> LogRange:
    """Exact port of ``autoLogRangeCertificate`` normalization."""
    if fuel < 0 or value <= 0:
        fail("invalid automatic log-range input")
    exponent = 0
    mantissa = value
    for _ in range(fuel):
        if mantissa < 1:
            mantissa *= 2
            exponent -= 1
        elif mantissa < 2:
            return LogRange(exponent, mantissa)
        else:
            mantissa /= 2
            exponent += 1
    return LogRange(exponent, mantissa)


def pow_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << -exponent)


def log_range_valid(value: Fraction, certificate: LogRange) -> bool:
    return (
        1 <= certificate.mantissa < 2
        and value == pow_two(certificate.exponent) * certificate.mantissa
    )


def log_range_enclosure(terms: int, certificate: LogRange) -> RatInterval:
    return rat_add(
        rat_scale(certificate.exponent, log_two_enclosure(terms)),
        log_mantissa_enclosure(terms, certificate.mantissa),
    )


def half_log_ratio_enclosure(terms: int,
                             coordinate: Fraction) -> RatInterval:
    return atanh_enclosure(terms, coordinate)


def half_log_one_sub_enclosure(terms: int, z: Fraction) -> RatInterval:
    if not 0 <= z < 1:
        fail("half-log-one-sub input outside [0,1)")
    return half_log_ratio_enclosure(terms, z / (2 - z))


def low_a(index: int) -> Fraction:
    if index < 1:
        fail("entropy coefficient index must be positive")
    return Fraction(1, 2 * index * (2 * index - 1))


def score_exact(r: Fraction, index: int) -> Fraction:
    if index < 1:
        fail("score index must be positive")
    return 1 - index * r ** (index - 1) + (index - 1) * r ** index


def w_lower_exact() -> Fraction:
    result = sum(
        (low_a(index) * score_exact(R_HI, index)
         for index in range(1, W_LOWER_TERMS + 1)),
        Fraction(0),
    )
    fraction_guard(result, "W lower head")
    return result


def coefficient_tail_enclosure(terms: int, index: int) -> RatInterval:
    prefix = sum((low_a(j) for j in range(1, index + 1)), Fraction(0))
    return rat_sub(log_two_enclosure(terms), RatInterval(prefix, prefix))


def w_abel_upper_exact() -> Fraction:
    """Upper endpoint of the existing degenerate-R Abel enclosure."""
    head = RatInterval(Fraction(0), Fraction(0))
    for index in range(1, W_ABEL_J + 1):
        term = rat_scale(
            index,
            rat_mul(
                coefficient_tail_enclosure(W_ABEL_TERMS, index),
                RatInterval(R_LO ** (index - 1), R_LO ** (index - 1)),
            ),
        )
        head = rat_add(head, term)
    gap_squared = (1 - R_LO) ** 2
    head = rat_scale(gap_squared, head)
    tail = (1 - R_LO) * R_LO ** W_ABEL_J / 4
    result = head.upper + tail
    fraction_guard(result, "W Abel upper")
    return result


def floor_scaled(value: Fraction) -> int:
    if value < 0:
        fail("cannot floor-scale a negative nonnegative endpoint")
    return value.numerator * SCALE // value.denominator


def ceil_scaled(value: Fraction) -> int:
    if value < 0:
        fail("cannot ceil-scale a negative nonnegative endpoint")
    numerator = value.numerator * SCALE
    return (numerator + value.denominator - 1) // value.denominator


def exact_scaled(value: Fraction, context: str) -> int:
    lower = floor_scaled(value)
    upper = ceil_scaled(value)
    if lower != upper:
        fail(f"{context}: expected an exactly representable dyadic")
    return lower


def ceil_div(value: int, divisor: int) -> int:
    if value < 0 or divisor <= 0:
        fail("invalid natural ceiling division")
    return (value + divisor - 1) // divisor


def mul_down(left: int, right: int) -> int:
    return left * right >> BITS


def mul_up(left: int, right: int) -> int:
    return (left * right + SCALE - 1) >> BITS


def nat_point(value: int) -> NatInterval:
    return NatInterval(value, value)


NAT_ZERO = nat_point(0)
NAT_ONE = nat_point(SCALE)
INT_ZERO = IntInterval(0, 0)


def nat_add(left: NatInterval, right: NatInterval) -> NatInterval:
    return NatInterval(left.lower + right.lower, left.upper + right.upper)


def nat_scale(value: NatInterval, coefficient: int) -> NatInterval:
    if coefficient < 0:
        fail("negative natural interval scale")
    return NatInterval(coefficient * value.lower, coefficient * value.upper)


def nat_mul(left: NatInterval, right: NatInterval) -> NatInterval:
    return NatInterval(
        mul_down(left.lower, right.lower),
        mul_up(left.upper, right.upper),
    )


def clamp_unit(value: NatInterval) -> NatInterval:
    return NatInterval(min(value.lower, SCALE), min(value.upper, SCALE))


def one_sub_unit(value: NatInterval) -> NatInterval:
    bounded = clamp_unit(value)
    return NatInterval(SCALE - bounded.upper, SCALE - bounded.lower)


def to_signed(value: NatInterval) -> IntInterval:
    return IntInterval(value.lower, value.upper)


def int_add(left: IntInterval, right: IntInterval) -> IntInterval:
    return IntInterval(left.lower + right.lower, left.upper + right.upper)


def int_neg(value: IntInterval) -> IntInterval:
    return IntInterval(-value.upper, -value.lower)


def int_sub(left: IntInterval, right: IntInterval) -> IntInterval:
    return int_add(left, int_neg(right))


def int_scale(value: IntInterval, coefficient: int) -> IntInterval:
    if coefficient < 0:
        fail("negative signed interval natural scale")
    return IntInterval(coefficient * value.lower, coefficient * value.upper)


def signed_mul_down(signed: int, nonnegative: int) -> int:
    if nonnegative < 0:
        fail("negative factor in signed/nonnegative multiplication")
    if signed >= 0:
        return mul_down(signed, nonnegative)
    return -mul_up(-signed, nonnegative)


def signed_mul_up(signed: int, nonnegative: int) -> int:
    if nonnegative < 0:
        fail("negative factor in signed/nonnegative multiplication")
    if signed >= 0:
        return mul_up(signed, nonnegative)
    return -mul_down(-signed, nonnegative)


def int_mul_nonnegative(signed: IntInterval,
                        nonnegative: NatInterval) -> IntInterval:
    lower_factor = (
        nonnegative.lower if signed.lower >= 0 else nonnegative.upper
    )
    upper_factor = (
        nonnegative.upper if signed.upper >= 0 else nonnegative.lower
    )
    return IntInterval(
        signed_mul_down(signed.lower, lower_factor),
        signed_mul_up(signed.upper, upper_factor),
    )


def signed_div_down(value: int, divisor: int) -> int:
    if divisor <= 0:
        fail("nonpositive signed divisor")
    if value >= 0:
        return value // divisor
    return -ceil_div(-value, divisor)


def signed_div_up(value: int, divisor: int) -> int:
    if divisor <= 0:
        fail("nonpositive signed divisor")
    if value >= 0:
        return ceil_div(value, divisor)
    return -((-value) // divisor)


def int_div(value: IntInterval, divisor: int) -> IntInterval:
    return IntInterval(
        signed_div_down(value.lower, divisor),
        signed_div_up(value.upper, divisor),
    )


def max_abs(value: IntInterval) -> int:
    return max(abs(value.lower), abs(value.upper))


def advance_score_endpoint(r: NatInterval, index: int,
                           state: ScoreEndpointState) -> ScoreEndpointState:
    return ScoreEndpointState(
        clamp_unit(nat_add(state.score,
                           nat_scale(state.increment_base, index))),
        nat_mul(state.increment_base, r),
    )


def initial_x_powers(x: NatInterval) -> XPowerState:
    return XPowerState(NAT_ONE, NAT_ONE, x)


def advance_x_powers(x: NatInterval, state: XPowerState) -> XPowerState:
    return XPowerState(state.previous, state.current,
                       nat_mul(state.current, x))


def initial_v_powers(v: NatInterval) -> VPowerState:
    return VPowerState(NAT_ONE, v)


def advance_v_powers(v_squared: NatInterval,
                     state: VPowerState) -> VPowerState:
    return VPowerState(nat_mul(state.even, v_squared),
                       nat_mul(state.odd, v_squared))


def u_shape(one_plus_v: NatInterval,
            powers: VPowerState) -> NatInterval:
    return nat_mul(one_plus_v, nat_add(NAT_ONE, powers.odd))


def u_derivative_shape(one_plus_v: NatInterval, powers: VPowerState,
                       index: int) -> NatInterval:
    odd = nat_add(NAT_ONE, powers.odd)
    weighted_even = nat_scale(nat_mul(one_plus_v, powers.even),
                              2 * index - 1)
    return nat_add(odd, weighted_even)


def two_nonnegative(signed: IntInterval, first: NatInterval,
                    second: NatInterval) -> IntInterval:
    return int_mul_nonnegative(int_mul_nonnegative(signed, first), second)


def coefficient(score_lower: ScoreEndpointState,
                score_upper: ScoreEndpointState,
                lambda_num: int) -> tuple[IntInterval, IntInterval]:
    score = clamp_unit(NatInterval(score_upper.score.lower,
                                   score_lower.score.upper))
    lambda_interval = nat_point(lambda_num)
    weighted_score = nat_mul(nat_add(NAT_ONE, lambda_interval), score)
    a_value = int_sub(to_signed(weighted_score), to_signed(lambda_interval))
    constant = to_signed(nat_scale(
        nat_mul(lambda_interval, one_sub_unit(score)), 4
    ))
    return a_value, constant


def p_contribution(index: int, a_value: IntInterval,
                   constant: IntInterval, powers: XPowerState,
                   u_value: NatInterval) -> IntInterval:
    varying = two_nonnegative(a_value, powers.current, u_value)
    return int_div(int_add(varying, constant),
                   2 * index * (2 * index - 1))


def pv_contribution(index: int, a_value: IntInterval,
                    powers: XPowerState,
                    u_derivative: NatInterval) -> IntInterval:
    return int_div(two_nonnegative(a_value, powers.current, u_derivative),
                   2 * index * (2 * index - 1))


def px_contribution(index: int, a_value: IntInterval,
                    powers: XPowerState,
                    u_value: NatInterval) -> IntInterval:
    return int_div(two_nonnegative(a_value, powers.previous, u_value),
                   2 * (2 * index - 1))


def pxx_contribution(index: int, a_value: IntInterval,
                     powers: XPowerState,
                     u_value: NatInterval) -> IntInterval:
    raw = two_nonnegative(a_value, powers.previous_previous, u_value)
    return int_div(int_scale(raw, index - 1), 2 * (2 * index - 1))


def evaluate_fixed(row: RowSpec, lambda_num: int,
                   common_r: NatInterval, common_x: NatInterval,
                   common_w: NatInterval) -> FixedOutput:
    v_full = NatInterval(exact_scaled(row.v_lo, "v lower"),
                         exact_scaled(row.v_hi, "v upper"))
    v_top = nat_point(v_full.upper)
    x_point = nat_point(exact_scaled(row.x_point, "x point"))
    r_bounded = clamp_unit(common_r)
    r_lower = nat_point(r_bounded.lower)
    r_upper = nat_point(r_bounded.upper)
    lower_gap = one_sub_unit(r_lower)
    upper_gap = one_sub_unit(r_upper)
    lower_score = ScoreEndpointState(NAT_ZERO,
                                     nat_mul(lower_gap, lower_gap))
    upper_score = ScoreEndpointState(NAT_ZERO,
                                     nat_mul(upper_gap, upper_gap))

    v_full_squared = nat_mul(v_full, v_full)
    v_top_squared = nat_mul(v_top, v_top)
    v_full_powers = initial_v_powers(v_full)
    v_top_powers = initial_v_powers(v_top)
    x_full_powers = initial_x_powers(common_x)
    x_point_powers = initial_x_powers(x_point)
    p_head = INT_ZERO
    pv_head = INT_ZERO
    px_head = INT_ZERO
    pxx_head = INT_ZERO

    for index in range(1, row.head + 1):
        a_value, constant = coefficient(lower_score, upper_score, lambda_num)
        top_u = u_shape(nat_add(NAT_ONE, v_top), v_top_powers)
        full_u_derivative = u_derivative_shape(
            nat_add(NAT_ONE, v_full), v_full_powers, index
        )
        p_head = int_add(p_head, p_contribution(
            index, a_value, constant, x_point_powers, top_u
        ))
        pv_head = int_add(pv_head, pv_contribution(
            index, a_value, x_full_powers, full_u_derivative
        ))
        px_powers = x_full_powers if row.mode == "corner" else x_point_powers
        px_head = int_add(px_head, px_contribution(
            index, a_value, px_powers, top_u
        ))
        if row.mode == "tangent":
            pxx_head = int_add(pxx_head, pxx_contribution(
                index, a_value, x_full_powers, top_u
            ))

        lower_score = advance_score_endpoint(r_lower, index, lower_score)
        upper_score = advance_score_endpoint(r_upper, index, upper_score)
        v_full_powers = advance_v_powers(v_full_squared, v_full_powers)
        v_top_powers = advance_v_powers(v_top_squared, v_top_powers)
        x_full_powers = advance_x_powers(common_x, x_full_powers)
        x_point_powers = advance_x_powers(x_point, x_point_powers)

    v_w = nat_mul(v_top, common_w)
    p_endpoint = to_signed(nat_scale(nat_mul(v_w, x_point), 4))
    pv_endpoint = to_signed(nat_scale(nat_mul(common_x, common_w), 4))
    px_endpoint = to_signed(nat_scale(v_w, 4))
    return FixedOutput(
        int_sub(p_head, p_endpoint),
        int_sub(pv_head, pv_endpoint),
        int_sub(px_head, px_endpoint),
        pxx_head,
    )


def same_y_data(row: RowSpec) -> tuple[LogRange, RatInterval,
                                       RatInterval, int, dict[str, bool]]:
    y_lo = row.v_lo ** 2 * X_LO
    if not (0 <= y_lo < 1 and 0 <= R_HI < 1):
        fail("invalid same-y row domain")
    log_certificate = auto_log_range(LOG_FUEL, 1 + row.v_hi)
    if not log_range_valid(1 + row.v_hi, log_certificate):
        fail("automatic log range did not validate")
    b_endpoint = rat_add(
        log_range_enclosure(LOG_TERMS, log_certificate),
        half_log_one_sub_enclosure(HALF_LOG_TERMS, R_HI * y_lo),
    )
    d_coordinate = (1 - R_HI) * y_lo / (2 - (1 + R_HI) * y_lo)
    d_endpoint = half_log_ratio_enclosure(D_TERMS, d_coordinate)
    d_lower = max(Fraction(0), d_endpoint.lower)
    if b_endpoint.upper <= 0 or d_lower <= 0:
        fail("nonpositive same-y endpoint data")
    lambda_num = floor_scaled(d_lower / b_endpoint.upper) - LAMBDA_GUARD_UNITS
    if lambda_num < 0:
        fail("lambda guard underflow")
    lambda_value = Fraction(lambda_num, SCALE)
    checks = {
        "directDValid": y_lo < 1 and R_HI < 1,
        "logRange": log_range_valid(1 + row.v_hi, log_certificate),
        "lambdaNonnegative": lambda_num >= 0,
        "budget": lambda_value * b_endpoint.upper <= d_lower,
        "slope": (
            lambda_value * R_HI * (1 - y_lo) <= 1 - R_HI
        ),
    }
    if not all(checks.values()):
        failed = [name for name, value in checks.items() if not value]
        fail(f"same-y checks failed: {failed}")
    return log_certificate, b_endpoint, d_endpoint, lambda_num, checks


def fraction_pair(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def interval_payload(value: IntInterval) -> dict[str, int]:
    return {"lower": value.lower, "upper": value.upper}


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True,
                       separators=(",", ": ")) + "\n").encode("ascii")


def lean_rat(numerator: int, denominator: int) -> str:
    if denominator <= 0:
        fail("Lean rational literal has nonpositive denominator")
    if denominator == 1:
        return f"({numerator} : ℚ)"
    return f"(({numerator} : ℚ) / {denominator})"


def lean_signed(value: int) -> str:
    return f"({value} : ℤ)"


def lean_nat_interval(value: dict[str, int]) -> str:
    return ("{ lower := " + str(value["lower"])
            + ", upper := " + str(value["upper"]) + " }")


def render_lean_literals(plan: dict[str, Any]) -> bytes:
    """Render one anonymous Lean record literal for the future adapter.

    The fragment intentionally declares no structures or external names.  It
    can be bound to the final leaf-core type once that API is fixed, without
    changing certificate arithmetic or the JSON schema.
    """
    common = plan["common"]
    row_literals = []
    for row in plan["rows"]:
        log_range = row["logOnePlusVHi"]
        observation = row["observation"]
        row_literals.append(
            "  { mode := ." + row["mode"]
            + ", head := " + str(row["head"])
            + ", v := { lower := " + str(row["vLowerNumerator"])
            + ", upper := " + str(row["vUpperNumerator"]) + " }"
            + ", xPoint := " + str(row["xPointNumerator"])
            + ", xRadius := " + str(row["xRadiusNumerator"])
            + ", lambdaNum := " + str(row["lambdaNumerator"])
            + ", logOnePlusVHi := { exponent := "
            + lean_signed(log_range["exponent"])
            + ", mantissa := "
            + lean_rat(log_range["mantissaNumerator"],
                       log_range["mantissaDenominator"]) + " }"
            + ", expected := { valueLower := "
            + lean_signed(observation["valueLower"])
            + ", vDerivativeUpper := "
            + lean_signed(observation["vDerivativeUpper"])
            + ", xAuxiliary := " + str(observation["xAuxiliary"])
            + ", xSecondDerivativeLower := "
            + lean_signed(observation["xSecondDerivativeLower"])
            + ", finalLower := " + lean_signed(row["finalLowerNumerator"])
            + " } }"
        )
    lower = common["rExactRange"]["lower"]
    upper = common["rExactRange"]["upper"]
    text = f"""/- Untrusted generated literal fragment.
Design SHA-256: {plan['designSha256']}
Observation SHA-256: {plan['observationSha256']}
Bind this anonymous record to the final centered-monotone leaf-core type. -/
{{ bits := {common['bits']}
  rLoExact := {lean_rat(lower[0], lower[1])}
  rHiExact := {lean_rat(upper[0], upper[1])}
  r := {lean_nat_interval(common['r'])}
  x := {lean_nat_interval(common['x'])}
  wOne := {lean_nat_interval(common['wOne'])}
  rows := #[
{',\n'.join(row_literals)}
  ] }}
"""
    return text.encode("utf-8")


def lean_row_literal(row: dict[str, Any]) -> str:
    """Render the fields of one production leaf-core ``Row`` value."""
    if row["head"] == 128:
        head = ".n128"
    elif row["head"] == 192:
        head = ".n192"
    else:
        fail(f"row {row['index']}: unsupported production head")
    if row["mode"] == "corner":
        geometry = ".corner"
    elif row["mode"] == "tangent":
        geometry = ".tangent " + str(row["xPointNumerator"])
    else:
        fail(f"row {row['index']}: unsupported production geometry")
    log_range = row["logOnePlusVHi"]
    return f"""vLoNum := {row['vLowerNumerator']}
vHiNum := {row['vUpperNumerator']}
lambdaNum := {row['lambdaNumerator']}
head := {head}
geometry := {geometry}
logOnePlusVHi :=
  {{ exponent := {lean_signed(log_range['exponent'])}
    mantissa := {lean_rat(log_range['mantissaNumerator'], log_range['mantissaDenominator'])} }}"""


def render_lean_config(plan: dict[str, Any]) -> bytes:
    """Render common data, exact path boxes, and the eight compact rows."""
    common = plan["common"]
    cuts = {
        index: lean_rat(ROWS[index].v_lo.numerator,
                        ROWS[index].v_lo.denominator)
        for index in range(1, len(ROWS))
    }
    rows = "\n\n".join(
        f"def row{row['index']} : Row where\n  "
        + lean_row_literal(row).replace("\n", "\n  ")
        for row in plan["rows"]
    )
    text = f"""import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneCheckedTreeCore

/-!
Untrusted generated data for the eight-strip centered-monotone replay.
Every arithmetic assertion is checked separately in the generated chunks;
this module contains only fixed data and exact subdivision paths.

Generator SHA-256: {plan['generatorSha256']}
Design SHA-256: {plan['designSha256']}
Observation SHA-256: {plan['observationSha256']}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {LEAN_NAMESPACE}

open LRCompactVCenteredMonotoneLeaf

def logTerms : ℕ := {common['logTerms']}
def halfLogTerms : ℕ := {common['halfLogTerms']}
def dTerms : ℕ := {common['dTerms']}

abbrev CheckedTree (root : CertificateBox) : Type :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree
    logTerms halfLogTerms dTerms root

def rootBox : CertificateBox :=
  LRCompactVCenteredMonotoneConfig.rootBox

def cut1 : ℚ := {cuts[LEFT_LEFT_SPLIT_INDEX]}
def cut2 : ℚ := {cuts[LEFT_SPLIT_INDEX]}
def cut3 : ℚ := {cuts[LEFT_RIGHT_SPLIT_INDEX]}
def cut4 : ℚ := {cuts[ROOT_SPLIT_INDEX]}
def cut5 : ℚ := {cuts[RIGHT_LEFT_SPLIT_INDEX]}
def cut6 : ℚ := {cuts[RIGHT_SPLIT_INDEX]}
def cut7 : ℚ := {cuts[RIGHT_RIGHT_SPLIT_INDEX]}

def boxL : CertificateBox := rootBox.lower .k cut4
def boxR : CertificateBox := rootBox.upper .k cut4
def boxLL : CertificateBox := boxL.lower .k cut2
def boxLR : CertificateBox := boxL.upper .k cut2
def boxRL : CertificateBox := boxR.lower .k cut6
def boxRR : CertificateBox := boxR.upper .k cut6

def box0 : CertificateBox := boxLL.lower .k cut1
def box1 : CertificateBox := boxLL.upper .k cut1
def box2 : CertificateBox := boxLR.lower .k cut3
def box3 : CertificateBox := boxLR.upper .k cut3
def box4 : CertificateBox := boxRL.lower .k cut5
def box5 : CertificateBox := boxRL.upper .k cut5
def box6 : CertificateBox := boxRR.lower .k cut7
def box7 : CertificateBox := boxRR.upper .k cut7

{rows}

end {LEAN_NAMESPACE}
end CourtadeKumar
"""
    return text.encode("utf-8")


def chunk_leaf_groups(chunk_size: int) -> list[list[int]]:
    if chunk_size not in ALLOWED_CHUNK_SIZES:
        fail(f"chunk size must be one of {ALLOWED_CHUNK_SIZES}")
    groups = [
        list(range(start, min(start + chunk_size, len(ROWS))))
        for start in range(0, len(ROWS), chunk_size)
    ]
    if [leaf for group in groups for leaf in group] != list(range(len(ROWS))):
        fail("segmented chunk partition lost or duplicated a leaf")
    return groups


def render_lean_chunk(plan: dict[str, Any], chunk_index: int,
                      leaves: list[int]) -> bytes:
    """Render one independently recoverable kernel arithmetic chunk."""
    if not leaves:
        fail("refusing to render an empty arithmetic chunk")
    declarations = []
    for leaf in leaves:
        declarations.append(f"""def leaf{leaf}Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box{leaf} row{leaf}

#kernel_checked_bool leaf{leaf}Check leaf{leaf}Result

def leaf{leaf}Checked : CheckedTree box{leaf} :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row{leaf} leaf{leaf}Check""")
    declarations_text = "\n\n".join(declarations)
    text = f"""import {LEAN_MODULE_PREFIX}.Config
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
Kernel arithmetic replay chunk {chunk_index:03d}; leaves {leaves}.
Design SHA-256: {plan['designSha256']}
Observation SHA-256: {plan['observationSha256']}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {LEAN_NAMESPACE}

open LRCompactVCenteredMonotoneLeaf

{declarations_text}

end {LEAN_NAMESPACE}
end CourtadeKumar
"""
    return text.encode("utf-8")


def render_lean_assembly(plan: dict[str, Any],
                         chunk_names: list[str]) -> bytes:
    """Render the arithmetic-free exact balanced checked-tree assembly."""
    imports = "\n".join(
        f"import {LEAN_MODULE_PREFIX}.{name}" for name in chunk_names
    )
    text = f"""{imports}

/-!
Arithmetic-free assembly of the eight independently kernel-checked leaves.
The joins reproduce the audited balanced k-subdivision exactly.

Design SHA-256: {plan['designSha256']}
Observation SHA-256: {plan['observationSha256']}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {LEAN_NAMESPACE}

open LRCompactVCenteredMonotoneLeaf

def nodeLL : CheckedTree boxLL :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut1 leaf0Checked leaf1Checked

def nodeLR : CheckedTree boxLR :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut3 leaf2Checked leaf3Checked

def nodeL : CheckedTree boxL :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut2 nodeLL nodeLR

def nodeRL : CheckedTree boxRL :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut5 leaf4Checked leaf5Checked

def nodeRR : CheckedTree boxRR :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut7 leaf6Checked leaf7Checked

def nodeR : CheckedTree boxR :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut6 nodeRL nodeRR

def checked : CheckedTree rootBox :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut4 nodeL nodeR

def certificate : SubdivisionCertificate Row Unit :=
  checked.certificate

theorem certificateCheck :
    certificate.check
      (Row.checkAt logTerms halfLogTerms dTerms)
      LRCompactVCenteredMonotoneCheckedTree.noDiscard rootBox = true := by
  exact checked.checked

end {LEAN_NAMESPACE}
end CourtadeKumar
"""
    return text.encode("utf-8")


def render_lean_certificate(plan: dict[str, Any]) -> bytes:
    """Render the one-import semantic endpoint of the generated family."""
    text = f"""import {LEAN_MODULE_PREFIX}.Assembly
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneCheckedTree

/-!
Semantic endpoint of the generated centered-monotone certificate.
Its only arithmetic inputs are the eight kernel theorems imported through
Assembly; this module performs no certificate computation.

Design SHA-256: {plan['designSha256']}
Observation SHA-256: {plan['observationSha256']}
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace {LEAN_NAMESPACE}

theorem target_nonnegative :
    ∀ point, rootBox.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.target_nonnegative checked

end {LEAN_NAMESPACE}
end CourtadeKumar
"""
    return text.encode("utf-8")


def validate_rendered_lean(sources: dict[str, bytes]) -> None:
    if not sources:
        fail("segmented Lean renderer produced no source files")
    total_bytes = sum(len(source) for source in sources.values())
    if total_bytes > MAX_SEGMENTED_OUTPUT_BYTES:
        fail(
            "segmented Lean output exceeds hard "
            f"{MAX_SEGMENTED_OUTPUT_BYTES}-byte guard"
        )
    joined = b"\n".join(sources[name] for name in sorted(sources))
    for token in LEAN_FORBIDDEN_TOKENS:
        if token.encode("ascii") in joined:
            fail(f"generated Lean contains forbidden token {token!r}")
    if joined.count(b"#kernel_checked_bool") != len(ROWS):
        fail("generated Lean does not contain exactly eight kernel leaf checks")
    if joined.count(b"Row.checkAt") != len(ROWS) + 1:
        # Eight leaf calls plus the checker named in certificateCheck.
        fail("generated Lean Row.checkAt count changed")
    for leaf in range(len(ROWS)):
        expected = (
            f"Row.checkAt logTerms halfLogTerms dTerms box{leaf} row{leaf}"
        ).encode("ascii")
        if expected not in joined:
            fail(f"leaf {leaf}: external path box is not authenticated")


def render_segmented_lean(plan: dict[str, Any],
                          chunk_size: int) -> dict[str, bytes]:
    """Render the complete recoverable production replay source bundle."""
    groups = chunk_leaf_groups(chunk_size)
    sources: dict[str, bytes] = {"Config.lean": render_lean_config(plan)}
    chunk_names = []
    for chunk_index, leaves in enumerate(groups):
        chunk_name = f"Chunk{chunk_index:03d}"
        chunk_names.append(chunk_name)
        sources[f"{chunk_name}.lean"] = render_lean_chunk(
            plan, chunk_index, leaves
        )
    sources["Assembly.lean"] = render_lean_assembly(plan, chunk_names)
    sources["Certificate.lean"] = render_lean_certificate(plan)
    validate_rendered_lean(sources)
    return sources


def segmented_manifest(plan: dict[str, Any], sources: dict[str, bytes],
                       chunk_size: int) -> tuple[dict[str, Any], str]:
    groups = chunk_leaf_groups(chunk_size)
    if chunk_size != DEFAULT_CHUNK_SIZE or len(groups) != 4:
        fail("production manifest requires exactly four two-leaf chunks")
    file_records = [
        {
            "path": name,
            "bytes": len(source),
            "sha256": hashlib.sha256(source).hexdigest(),
        }
        for name, source in sorted(sources.items())
    ]
    manifest_core = {
        "format": "lr-compact-v-centered-monotone-lean-bundle-v1",
        "untrustedGenerator": True,
        "generatorSha256": plan["generatorSha256"],
        "designSha256": plan["designSha256"],
        "observationSha256": plan["observationSha256"],
        "rowCount": plan["rowCount"],
        "weightedHeadCount": plan["weightedHeadCount"],
        "chunkSize": chunk_size,
        "leafChunks": [
            {
                "module": f"{LEAN_MODULE_PREFIX}.Chunk{index:03d}",
                "path": f"Chunk{index:03d}.lean",
                "leaves": leaves,
            }
            for index, leaves in enumerate(groups)
        ],
        "assemblyModule": f"{LEAN_MODULE_PREFIX}.Assembly",
        "certificateModule": f"{LEAN_MODULE_PREFIX}.Certificate",
        "files": file_records,
    }
    bundle_hash = hashlib.sha256(canonical_bytes(manifest_core)).hexdigest()
    return {**manifest_core, "bundleSha256": bundle_hash}, bundle_hash


def fixed_design_payload() -> dict[str, Any]:
    return {
        "bits": BITS,
        "rRange": {"lower": fraction_pair(R_LO),
                   "upper": fraction_pair(R_HI)},
        "xRange": {"lower": fraction_pair(X_LO),
                   "upper": fraction_pair(X_HI)},
        "logTerms": LOG_TERMS,
        "halfLogTerms": HALF_LOG_TERMS,
        "dTerms": D_TERMS,
        "logFuel": LOG_FUEL,
        "lambdaGuardUnits": LAMBDA_GUARD_UNITS,
        "wConstruction": {
            "lowerScoreTerms": W_LOWER_TERMS,
            "abelLogTerms": W_ABEL_TERMS,
            "abelJ": W_ABEL_J,
        },
        "rows": [
            {
                "vLower": fraction_pair(row.v_lo),
                "vUpper": fraction_pair(row.v_hi),
                "head": row.head,
                "mode": row.mode,
                "xPoint": fraction_pair(row.x_point),
            }
            for row in ROWS
        ],
    }


def validate_fixed_design() -> None:
    if len(ROWS) != MAX_ROWS:
        fail("fixed row count changed")
    if any(row.mode not in {"corner", "tangent"} for row in ROWS):
        fail("unknown terminal mode")
    if any(row.head not in {128, 192} or row.head > MAX_HEAD for row in ROWS):
        fail("head outside fixed resource policy")
    if sum(row.head for row in ROWS) != EXPECTED_WEIGHTED_HEADS:
        fail("weighted-head resource guard changed")
    if ROWS[0].v_lo != Fraction(15, 16) or ROWS[-1].v_hi != Fraction(31, 32):
        fail("fixed strips do not cover the intended v range")
    expected_boundaries = tuple(Fraction(value, 512) for value in
                                (480, 484, 487, 489, 491,
                                 493, 494, 495, 496))
    actual_boundaries = (ROWS[0].v_lo,) + tuple(row.v_hi for row in ROWS)
    if actual_boundaries != expected_boundaries:
        fail("fixed nonuniform strip boundary sequence changed")
    for index, row in enumerate(ROWS):
        if index and ROWS[index - 1].v_hi != row.v_lo:
            fail(f"row {index}: v strips are not adjacent")
        if not X_LO <= row.x_point <= X_HI:
            fail(f"row {index}: x point lies outside the common interval")


def validate_balanced_topology() -> None:
    """Authenticate the fixed balanced subdivision independently of rendering."""
    split_indices = (
        ROOT_SPLIT_INDEX,
        LEFT_SPLIT_INDEX,
        LEFT_LEFT_SPLIT_INDEX,
        LEFT_RIGHT_SPLIT_INDEX,
        RIGHT_SPLIT_INDEX,
        RIGHT_LEFT_SPLIT_INDEX,
        RIGHT_RIGHT_SPLIT_INDEX,
    )
    if split_indices != (4, 2, 1, 3, 6, 5, 7):
        fail("balanced subdivision split indices changed")
    expected_cuts = (
        Fraction(491, 512),
        Fraction(487, 512),
        Fraction(121, 128),
        Fraction(489, 512),
        Fraction(247, 256),
        Fraction(493, 512),
        Fraction(495, 512),
    )
    actual_cuts = tuple(ROWS[index].v_lo for index in split_indices)
    if actual_cuts != expected_cuts:
        fail("balanced subdivision cuts changed")

    # These intervals are the leaves reached by the exact lower/upper path
    # encoded in Config.lean and later joined in Assembly.lean.
    expected_leaf_intervals = tuple(
        (Fraction(value_lo, 512), Fraction(value_hi, 512))
        for value_lo, value_hi in (
            (480, 484), (484, 487), (487, 489), (489, 491),
            (491, 493), (493, 494), (494, 495), (495, 496),
        )
    )
    actual_leaf_intervals = tuple((row.v_lo, row.v_hi) for row in ROWS)
    if actual_leaf_intervals != expected_leaf_intervals:
        fail("balanced subdivision leaf paths no longer match row intervals")


def build_plan() -> tuple[dict[str, Any], dict[str, Any]]:
    validate_fixed_design()
    validate_balanced_topology()
    design = fixed_design_payload()
    design_hash = hashlib.sha256(canonical_bytes(design)).hexdigest()
    if design_hash != EXPECTED_DESIGN_SHA256:
        fail("fixed design hash no longer matches the audited eight rows")
    generator_hash = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()

    common_r = NatInterval(floor_scaled(R_LO), ceil_scaled(R_HI))
    common_x = NatInterval(exact_scaled(X_LO, "common x lower"),
                           exact_scaled(X_HI, "common x upper"))
    common_w = NatInterval(floor_scaled(w_lower_exact()),
                           ceil_scaled(w_abel_upper_exact()))
    if common_w != NatInterval(EXPECTED_W_LOWER_NUMERATOR,
                               EXPECTED_W_UPPER_NUMERATOR):
        fail("sharp W construction no longer matches audited numerators")

    generated_rows: list[dict[str, Any]] = []
    budget_slacks: list[Fraction] = []
    slope_slacks: list[Fraction] = []
    final_lowers: list[int] = []
    for index, row in enumerate(ROWS):
        log_range, b_endpoint, d_endpoint, lambda_num, checks = same_y_data(row)
        if lambda_num != EXPECTED_LAMBDA_NUMERATORS[index]:
            fail(f"row {index}: lambda numerator changed from audited value")
        output = evaluate_fixed(row, lambda_num, common_r, common_x, common_w)
        if row.mode == "corner":
            auxiliary = output.px.upper
            final_lower = output.p.lower
            terminal_checks = {
                "vDecreasing": output.pv.upper <= 0,
                "xDecreasing": output.px.upper <= 0,
                "finalNonnegative": final_lower >= 0,
            }
            x_radius_num = 0
        else:
            auxiliary = max_abs(output.px)
            center_num = exact_scaled(row.x_point, "tangent center")
            x_radius_num = max(center_num - common_x.lower,
                               common_x.upper - center_num)
            loss_upper = mul_up(auxiliary, x_radius_num)
            final_lower = output.p.lower - loss_upper
            terminal_checks = {
                "vDecreasing": output.pv.upper <= 0,
                "xConvex": output.pxx.lower >= 0,
                "finalNonnegative": final_lower >= 0,
            }
        if not all(terminal_checks.values()):
            failed = [name for name, value in terminal_checks.items()
                      if not value]
            fail(f"row {index}: terminal checks failed: {failed}")

        y_lo = row.v_lo ** 2 * X_LO
        lambda_value = Fraction(lambda_num, SCALE)
        d_lower = max(Fraction(0), d_endpoint.lower)
        budget_slacks.append(d_lower - lambda_value * b_endpoint.upper)
        slope_slacks.append(
            1 - R_HI - lambda_value * R_HI * (1 - y_lo)
        )
        final_lowers.append(final_lower)
        generated_rows.append({
            "index": index,
            "mode": row.mode,
            "head": row.head,
            "vLowerNumerator": exact_scaled(row.v_lo, "row v lower"),
            "vUpperNumerator": exact_scaled(row.v_hi, "row v upper"),
            "xPointNumerator": exact_scaled(row.x_point, "row x point"),
            "xRadiusNumerator": x_radius_num,
            "lambdaNumerator": lambda_num,
            "logOnePlusVHi": {
                "exponent": log_range.exponent,
                "mantissaNumerator": log_range.mantissa.numerator,
                "mantissaDenominator": log_range.mantissa.denominator,
            },
            "observation": {
                "valueLower": output.p.lower,
                "vDerivativeUpper": output.pv.upper,
                "xAuxiliary": auxiliary,
                "xSecondDerivativeLower": (
                    output.pxx.lower if row.mode == "tangent" else 0
                ),
            },
            "finalLowerNumerator": final_lower,
            "checks": {**checks, **terminal_checks},
        })

    observation_guard = [
        {
            "lambdaNumerator": row["lambdaNumerator"],
            "observation": row["observation"],
            "finalLowerNumerator": row["finalLowerNumerator"],
        }
        for row in generated_rows
    ]
    observation_hash = hashlib.sha256(
        canonical_bytes(observation_guard)
    ).hexdigest()
    if observation_hash != EXPECTED_OBSERVATION_SHA256:
        fail("lambda/observation rows no longer match the audited replay")
    plan = {
        "format": "lr-compact-v-centered-monotone-plan-v1",
        "untrustedGenerator": True,
        "generatorSha256": generator_hash,
        "designSha256": design_hash,
        "observationSha256": observation_hash,
        "common": {
            "bits": BITS,
            "scale": SCALE,
            "logTerms": LOG_TERMS,
            "halfLogTerms": HALF_LOG_TERMS,
            "dTerms": D_TERMS,
            "logFuel": LOG_FUEL,
            "rExactRange": {
                "lower": fraction_pair(R_LO),
                "upper": fraction_pair(R_HI),
            },
            "r": asdict(common_r),
            "x": asdict(common_x),
            "wOne": asdict(common_w),
            "wConstruction": design["wConstruction"],
        },
        "rowCount": len(generated_rows),
        "weightedHeadCount": sum(row.head for row in ROWS),
        "rows": generated_rows,
    }
    summary = {
        "designSha256": design_hash,
        "observationSha256": observation_hash,
        "rowCount": len(generated_rows),
        "weightedHeadCount": sum(row.head for row in ROWS),
        "minimumFinalLowerNumerator": min(final_lowers),
        "minimumBudgetSlackPositive": min(budget_slacks) > 0,
        "minimumSlopeSlack": str(min(slope_slacks)),
    }
    return plan, summary


def atomic_write(path: Path, data: bytes, force: bool) -> None:
    if len(data) > MAX_OUTPUT_BYTES:
        fail(f"output exceeds hard {MAX_OUTPUT_BYTES}-byte guard")
    if path.exists():
        if path.read_bytes() == data:
            return
        if not force:
            fail(f"refusing to replace differing {path}; pass --force")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".building")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def atomic_write_bundle(directory: Path, files: dict[str, bytes],
                        force: bool) -> None:
    """Preflight then atomically replace each owned file in one bundle."""
    if directory.exists() and not directory.is_dir():
        fail(f"segmented output target is not a directory: {directory}")
    for name, data in files.items():
        path = directory / name
        if path.exists() and path.read_bytes() != data and not force:
            fail(f"refusing to replace differing {path}; pass --force")
    directory.mkdir(parents=True, exist_ok=True)
    for name, data in files.items():
        atomic_write(directory / name, data, force)


def generate(output: Path | None, force: bool,
             output_format: str,
             chunk_size: int = DEFAULT_CHUNK_SIZE) -> dict[str, Any]:
    plan, summary = build_plan()
    if output_format == "lean-segmented":
        if output is None:
            fail("--format lean-segmented requires --output DIRECTORY")
        sources = render_segmented_lean(plan, chunk_size)
        manifest, bundle_hash = segmented_manifest(
            plan, sources, chunk_size
        )
        manifest_bytes = canonical_bytes(manifest)
        files = {**sources, "manifest.json": manifest_bytes}
        total_bytes = sum(len(data) for data in files.values())
        if total_bytes > MAX_SEGMENTED_OUTPUT_BYTES:
            fail(
                "segmented bundle exceeds hard "
                f"{MAX_SEGMENTED_OUTPUT_BYTES}-byte guard"
            )
        atomic_write_bundle(output, files, force)
        summary = {
            **summary,
            "outputSha256": bundle_hash,
            "outputBytes": total_bytes,
            "chunkSize": chunk_size,
            "chunkCount": len(chunk_leaf_groups(chunk_size)),
            "outputFiles": sorted(files),
        }
        print(json.dumps(summary, sort_keys=True))
        return summary
    if output_format == "json":
        encoded = canonical_bytes(plan)
    elif output_format == "lean-literals":
        encoded = render_lean_literals(plan)
    else:
        fail(f"unknown output format {output_format!r}")
    output_hash = hashlib.sha256(encoded).hexdigest()
    summary = {**summary, "outputSha256": output_hash,
               "outputBytes": len(encoded)}
    if output is None:
        sys.stdout.buffer.write(encoded)
    else:
        atomic_write(output, encoded, force)
        print(json.dumps(summary, sort_keys=True))
    return summary


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "--output",
        type=Path,
        help=(
            "write one output file atomically, or the segmented Lean bundle "
            "to this directory; omit only for single-file stdout output"
        ),
    )
    result.add_argument(
        "--force",
        action="store_true",
        help="replace a differing output file",
    )
    result.add_argument(
        "--format",
        choices=("json", "lean-literals", "lean-segmented"),
        default="json",
        help=(
            "emit the JSON plan, an API-neutral literal fragment, or the "
            "four-chunk production Lean bundle"
        ),
    )
    result.add_argument(
        "--chunk-size",
        type=int,
        choices=ALLOWED_CHUNK_SIZES,
        default=DEFAULT_CHUNK_SIZE,
        help="production leaves per independently recoverable arithmetic chunk",
    )
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(list(argv) if argv is not None else None)
    if args.force and args.output is None:
        fail("--force requires --output")
    generate(args.output, args.force, args.format, args.chunk_size)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GenerationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
