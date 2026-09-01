#!/usr/bin/env python3
"""Bounded Compact-V benchmark for combined leaf and split reductions.

This is a diagnostic benchmark, not a certificate generator.  It compares
the following three default modes on both ``adjacent-high`` and
``extreme-high`` roots while holding the DirectD/Psi assembly fixed:

``tail-directd-old``
    The tail-enhanced P lower bound inside the current DirectD/Psi assembly,
    followed by the normalized-width split.
``hybrid-old``
    The maximum of the tail-enhanced and direct-positive-head lower bounds,
    followed by the same normalized-width split.
``hybrid-lookahead``
    The hybrid lower bound followed by deterministic one-step lookahead.

The optional ``historical-baseline`` mode uses the older Python tail/full-D
lower bound.  It is an explicitly non-controlled historical comparison: it
does not replay the current DirectD leaf and is not used in the default matrix.

For a box b=[r_l,r_h]x[v_l,v_h]x[x_l,x_h], the hybrid first forms

    P_tail = lower(w_(N+1)(r_h) A0_lower(v_l,x_l)) - E_N_upper(b),
    P_head = lower(sum_(n=1)^N a_n w_n(r_h)
                              x_l^n (1+v_l^(2n-1))),
    P_lower = max(P_tail, P_head),
    Q_lower = P_lower - upper(4 W(r_l) v_h x_h/(1+v_h)).

It then returns the current checker-shaped, sign-safe lower bound

    L_V = B_sigma Q_lower + max(0,D_direct_lower)
                                  max(0,Psi_polynomial_lower),

where B_sigma is B_lower when Q_lower>=0 and B_upper otherwise.  Put

    y_lower = v_l^2 x_l,
    q_D = (1-r_h)y_lower / (2-(1+r_h)y_lower).

``D_direct_lower`` is the lower endpoint of the first ``dTerms`` positive
terms of ``atanh(q_D)``.  ``Psi_polynomial_lower`` starts from zero and sums
only ``a_n (4/(1+v)-T_n)(1-w_n)`` for ``1<=n<=N``; the nonnegative ``f0``
term is deliberately omitted.  These choices mirror
``LRCompactVHybridDirectDLeafCertificate.groupedLower``.  The required
DirectD validity checks are ``r_h<1`` and ``v_l^2 x_l<1``.

A box is discarded exactly when the computed upper bound ``J_upper<=0``,
and is accepted exactly when its active lower bound is nonnegative.  The
finite P_W head is sound because every omitted series term is nonnegative;
the corresponding semantic theorem is ``lrCompactVPWHead_le_lrFlowPW``.

For every unresolved box, ``hybrid-lookahead`` evaluates both midpoint
children on all three axes and maximizes

    (closed children, minimum child lower, sum child lowers, -axis).

Here a J<=0 discard is represented by ``10**100`` in the two lower-bound
fields, and axes are R=0, v=1, x=2.  Thus exact ties prefer R, then v, then x.
Lookahead changes only the tree topology: acceptance still uses the hybrid
predicate above.

The optional ``hybrid-lambda-old``, ``hybrid-lookahead-lambda-close``, and
``hybrid-lambda-lookahead`` modes add the independently sound grouped test
from the high-corner experiment.  They accept only if its lower bound for
Q+lambda*C is nonnegative.  ``hybrid-lookahead-lambda-close`` retains the
primary-bound lookahead topology and uses lambda only to close the current
box.  ``hybrid-lambda-lookahead`` additionally converts lambda child bounds
to reserve units with a sign-safe box-wide B endpoint and includes them in
the split score.  These exploratory modes are not used in the default matrix.

The formal DirectD checker does not use the J-dependent physical shape cap,
so this benchmark defaults to no cap.  ``--physical-cap`` is available only
as a separately labelled, sound-on-the-physical-domain experiment and is not
checker-fidelity evidence.

The topology predictor still uses the imported Q132 dyadic Python engine.
In particular, its tail-enhanced P bound and ``W_upper`` truncation are not
bit-for-bit the exact-rational/log-certificate computations replayed by Lean.
Consequently matching the DirectD/Psi predicate does not make a reported
terminal count an exact forecast of the Lean generator.

All traversals are depth first and depth limited.  The default six runs share
one 200,000-node/120-second budget, divided equally between runs.  A global
deadline also bounds total traversal time, so a run late in the requested
order can receive slightly less time after setup and cache-clearing overhead.
Limits are checked between interval evaluations.  Large caches are cleared
periodically and between runs; progress and process-cumulative peak-RSS
statistics go to stderr, while the final machine-readable comparison goes to
stdout.  Head/tail win counters count every primary-bound evaluation,
including speculative lookahead children.

Examples (run from the ChatGPT project mirror root):

  python3 lean-formalization/scripts/benchmark_compact_v_combined_reductions.py
  python3 lean-formalization/scripts/benchmark_compact_v_combined_reductions.py \
      --regions adjacent-high --cutoff-depth 18 --max-nodes 100000
  python3 lean-formalization/scripts/benchmark_compact_v_combined_reductions.py \
      --include-lambda-lookahead
"""

from __future__ import annotations

import argparse
import gc
import hashlib
import json
import math
import resource
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from time import monotonic


LEAN_ROOT = Path(__file__).resolve().parents[1]
PROJECT_ROOT = LEAN_ROOT.parent
sys.path.insert(0, str(PROJECT_ROOT))

import verify_lr_compact_R34_V_interval as q  # noqa: E402
import verify_lr_midcompact_V_interval as m  # noqa: E402


RLO = "921/1024"
RHI = "9/10"
TAIL_N = 64
D_TERMS = 34
V_SENSITIVITY = 16
X_SENSITIVITY = 8
DISCARD_SENTINEL = 10**100
AXIS_NAMES = ("R", "v", "x")
DEFAULT_REGIONS = ("adjacent-high", "extreme-high")
DEFAULT_MODES = ("tail-directd-old", "hybrid-old", "hybrid-lookahead")


@dataclass(frozen=True, slots=True)
class Region:
    vlo: str
    vhi: str
    xlo: str
    xhi: str


REGIONS = {
    # The actual full compact-V slab used by the Lean soundness theorem.
    "full-slab": Region("1/3", "1", "17/20", "1"),
    # The canary on which the original lookahead experiment sharply reduced
    # the terminal count.
    "adjacent-high": Region("15/16", "31/32", "63/64", "127/128"),
    # Contains the narrow physical/J boundary and the audited deep leaves.
    "extreme-high": Region("31/32", "1", "127/128", "1"),
}


@dataclass(frozen=True, slots=True)
class ModeSpec:
    primary_bound: str
    split_policy: str
    lambda_grouped: bool = False
    lambda_lookahead_score: bool = False


MODES = {
    "historical-baseline": ModeSpec("historical", "old"),
    "tail-directd-old": ModeSpec("tail-directd", "old"),
    "hybrid-old": ModeSpec("hybrid", "old"),
    "hybrid-lookahead": ModeSpec("hybrid", "lookahead"),
    "hybrid-lambda-old": ModeSpec("hybrid", "old", lambda_grouped=True),
    "hybrid-lookahead-lambda-close": ModeSpec(
        "hybrid", "lookahead", lambda_grouped=True
    ),
    "hybrid-lambda-lookahead": ModeSpec(
        "hybrid",
        "lookahead",
        lambda_grouped=True,
        lambda_lookahead_score=True,
    ),
}


@dataclass(frozen=True, slots=True)
class PrimaryBound:
    lower: int | None
    j_upper: int
    source: str
    direct_d_valid: bool = True


def parse_outward(text: str, *, upper: bool) -> int:
    return m.parse_fraction(text, upper=upper)


def source_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def peak_rss() -> tuple[int, float]:
    """Return the platform counter and its normalized value in MiB."""
    raw = int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    # Darwin reports bytes; Linux and the other supported benchmark hosts
    # report KiB.  Retain the raw value as well as the normalized diagnostic.
    byte_count = raw if sys.platform == "darwin" else raw * 1024
    return raw, byte_count / (1024 * 1024)


@lru_cache(maxsize=16_384)
def direct_pw_head_lower(r_hi: int, v_lo: int, x_lo: int, tail_n: int) -> int:
    """Lower endpoint of the positive P_W head through ``tail_n``."""
    xx = q.point(x_lo)
    vv = q.point(v_lo)
    v2 = q.square(vv)
    x_power = xx
    odd_v_power = vv
    total = q.ZERO
    for n in range(1, tail_n + 1):
        shape = q.mul(x_power, q.add(q.UNIT, odd_v_power))
        term = q.mul(
            q.mul(q.acoef(n), m.wscore(n, r_hi, tail_n)),
            shape,
        )
        total = q.add(total, term)
        x_power = q.mul(x_power, xx)
        odd_v_power = q.mul(odd_v_power, v2)
    return total.lo


def direct_d_valid(box: m.Box) -> bool:
    """Exact dyadic form of the two extra DirectD validity inequalities."""
    exact_y_numerator = box.vl * box.vl * box.xl
    return (
        box.rh < q.ONE
        and exact_y_numerator < q.ONE * q.ONE * q.ONE
    )


@lru_cache(maxsize=16_384)
def direct_d_lower(r_hi: int, v_lo: int, x_lo: int, d_terms: int) -> int:
    """Direct half-log lower bound at (r_hi, v_lo^2*x_lo).

    The exact rational coordinate is

        q_D=(1-r_hi)y_lo/(2-(1+r_hi)y_lo).

    ``halfLogRatioEnclosure`` has lower endpoint equal to the first
    ``d_terms`` terms of the positive atanh series.  The interval recurrence
    below outward-rounds that same rational calculation to the engine's
    common dyadic denominator.
    """
    exact_y_numerator = v_lo * v_lo * x_lo
    exact_y_denominator = q.ONE * q.ONE * q.ONE
    assert r_hi < q.ONE
    assert exact_y_numerator < exact_y_denominator
    coordinate_numerator = (q.ONE - r_hi) * exact_y_numerator
    coordinate_denominator = (
        2 * q.ONE * exact_y_denominator
        - (q.ONE + r_hi) * exact_y_numerator
    )
    coordinate = q.rat(coordinate_numerator, coordinate_denominator)
    coordinate_squared = q.square(coordinate)
    term = coordinate
    total = q.ZERO
    for index in range(d_terms):
        total = q.add(total, q.scale_rat(term, 1, 2 * index + 1))
        term = q.mul(term, coordinate_squared)
    return total.lo


@lru_cache(maxsize=16_384)
def psi_polynomial_head_lower(
    rl: int,
    rh: int,
    vl: int,
    vh: int,
    xh: int,
    tail_n: int,
    use_physical_cap: bool,
) -> int:
    """Nonnegative lower bound for the polynomial Psi head, without f0."""
    total = q.ZERO
    shape_uppers = m.physical_shape_uppers(
        rh, vl, vh, xh, tail_n, use_physical_cap
    )
    four_over_one_plus_v = q.scale_int(
        q.div(q.UNIT, q.point(q.ONE + vh)), 4
    )
    for n in range(1, tail_n + 1):
        c_lower = max(0, four_over_one_plus_v.lo - shape_uppers[n])
        one_minus_w_lower = max(
            0, q.ONE - m.wscore(n, rl, tail_n).hi
        )
        total = q.add(
            total,
            q.mul(
                q.mul(q.acoef(n), q.point(c_lower)),
                q.point(one_minus_w_lower),
            ),
        )
    return max(0, total.lo)


def hybrid_box_lower_bound(
    box: m.Box,
    tail_n: int,
    d_terms: int,
    difference_modes: tuple[int, ...],
    use_physical_cap: bool,
    *,
    use_direct_head: bool,
) -> PrimaryBound:
    """Return the checker-shaped DirectD lower bound for one box.

    When ``use_direct_head`` is false, the P component is forced to the
    tail-enhanced lower bound.  This supplies a controlled baseline for the
    hybrid maximum without changing any other part of the leaf predicate.
    """
    rl, rh = box.rl, box.rh
    vl, vh = box.vl, box.vh
    xl, xh = box.xl, box.xh

    blo = q.B_lower(rl, vl, xl)
    bhi = q.B_upper(rh, vh, xh)
    jhi = q.mul(q.point(q.ONE + xh), q.point(bhi)).hi - q.A_lower(vl, xl)
    if jhi <= 0:
        return PrimaryBound(None, jhi, "discard")
    if not direct_d_valid(box):
        return PrimaryBound(
            -DISCARD_SENTINEL, jhi, "invalid-direct-d", False
        )

    a0lo = q.A0_lower(vl, xl)
    eup = m.E_upper(
        rl,
        rh,
        vl,
        vh,
        xh,
        tail_n,
        difference_modes,
        use_physical_cap,
    )
    terminal_weight = m.wscore(tail_n + 1, rh, tail_n).lo
    tail_lower = q.mul(q.point(terminal_weight), q.point(a0lo)).lo - eup
    if use_direct_head:
        head_lower = direct_pw_head_lower(rh, vl, xl, tail_n)
    else:
        head_lower = tail_lower
    if use_direct_head and head_lower > tail_lower:
        plow = head_lower
        source = "head"
    else:
        plow = tail_lower
        source = "tail"

    mxhi = q.div(
        q.mul(q.point(vh), q.point(xh)), q.point(q.ONE + vh)
    ).hi
    qlow = plow - q.scale_int(
        q.mul(q.point(q.W_upper(rl)), q.point(mxhi)), 4
    ).hi
    dlo = max(0, direct_d_lower(rh, vl, xl, d_terms))
    psi_lower = psi_polynomial_head_lower(
        rl, rh, vl, vh, xh, tail_n, use_physical_cap
    )
    bq = q.mul(q.point(blo if qlow >= 0 else bhi), q.point(qlow)).lo
    payment = q.mul(q.point(dlo), q.point(psi_lower)).lo
    return PrimaryBound(bq + payment, jhi, source)


def t_lower(vl: int, xl: int, n: int) -> int:
    return q.mul(
        q.pow_nat(q.point(xl), n),
        q.add(q.UNIT, q.pow_nat(q.point(vl), 2 * n - 1)),
    ).lo


def bilinear_group_lower(
    wlo: int,
    whi: int,
    tlo: int,
    thi: int,
    lam: int,
    glo: int,
    hup: int,
) -> int:
    """Lower bound for w(T-h)+lambda(1-w)(g-T)."""
    values: list[int] = []
    for weight in (wlo, whi):
        for shape in (tlo, thi):
            first = q.mul(q.point(weight), q.point(shape - hup))
            second = q.mul(
                q.mul(q.point(lam), q.point(q.ONE - weight)),
                q.point(glo - shape),
            )
            values.append(q.add(first, second).lo)
    return min(values)


@lru_cache(maxsize=8_192)
def lambda_grouped_lower(
    rl: int,
    rh: int,
    vl: int,
    vh: int,
    xl: int,
    xh: int,
    head_n: int,
    use_physical_cap: bool,
) -> tuple[int, int, int, int]:
    """Return (S_lower, lambda_lower, D_endpoint_lower, B_endpoint_upper).

    ``S_lower`` bounds Q+lambda*C from below.  The tight-ratio construction
    uses the same endpoint (rh,vh,ylo) in D/B, includes f0, and is the default
    sound variant from ``experiment_compact_v_lambda_grouped.py``.
    """
    ylo = q.product_lower(vl, vl, xl)
    dlo = max(0, m.D_full_lower(rh, ylo))
    rylo_up = q.mul(q.point(rh), q.point(ylo)).hi
    bhi = q.add(q.beta_scalar(vh), q.ell_scalar(rylo_up)).hi
    lam = q.div(q.point(dlo), q.point(bhi)).lo

    glo = q.scale_int(q.div(q.UNIT, q.point(q.ONE + vh)), 4).lo
    hup = q.scale_int(
        q.div(
            q.mul(q.point(vh), q.point(xh)),
            q.point(q.ONE + vh),
        ),
        4,
    ).hi
    f0lo = max(
        0,
        q.g_scalar(vh).lo
        - q.scale_int(q.div(q.LOG2, q.point(q.ONE + vh)), 4).hi,
    )
    total = q.mul(q.point(lam), q.point(f0lo)).lo

    shape_uppers = m.physical_shape_uppers(
        rh, vl, vh, xh, head_n, use_physical_cap
    )
    weighted_head_lower = q.ZERO
    for n in range(1, head_n + 1):
        wlo = m.wscore(n, rh, head_n).lo
        whi = m.wscore(n, rl, head_n).hi
        grouped = bilinear_group_lower(
            wlo,
            whi,
            t_lower(vl, xl, n),
            shape_uppers[n],
            lam,
            glo,
            hup,
        )
        total = q.add(
            q.point(total), q.mul(q.acoef(n), q.point(grouped))
        ).lo
        weighted_head_lower = q.add(
            weighted_head_lower, q.mul(q.acoef(n), q.point(wlo))
        )

    weighted_tail_upper = max(0, q.W_upper(rl) - weighted_head_lower.lo)
    tail_penalty = q.mul(q.point(hup), q.point(weighted_tail_upper)).hi
    return total - tail_penalty, lam, dlo, bhi


def lambda_grouped_reserve_lower(box: m.Box, grouped_lower: int) -> int:
    """Convert a lower bound for Q+lambda*C to reserve-value units.

    The multiplier is the full box-wide B endpoint, not the tight-ratio B
    endpoint returned by ``lambda_grouped_lower``.  Since B is positive, its
    lower endpoint is sign-safe for a nonnegative grouped lower bound and its
    upper endpoint is sign-safe for a negative one.
    """
    if grouped_lower >= 0:
        multiplier = q.B_lower(box.rl, box.vl, box.xl)
    else:
        multiplier = q.B_upper(box.rh, box.vh, box.xh)
    return q.mul(q.point(multiplier), q.point(grouped_lower)).lo


def evaluate_lambda_grouped(
    box: m.Box,
    grouped_head_n: int,
    use_physical_cap: bool,
    counters: dict[str, int],
    runtime: RuntimeCounters,
) -> tuple[int, int]:
    """Return grouped and reserve-unit lower bounds, updating diagnostics."""
    grouped_lower, _lam, _dlo, _ratio_bhi = lambda_grouped_lower(
        box.rl,
        box.rh,
        box.vl,
        box.vh,
        box.xl,
        box.xh,
        grouped_head_n,
        use_physical_cap,
    )
    counters["groupedBoundEvaluations"] += 1
    runtime.note_interval_evaluation()
    return grouped_lower, lambda_grouped_reserve_lower(box, grouped_lower)


def clear_large_caches() -> None:
    """Clear every large cache added or used by this benchmark."""
    direct_pw_head_lower.cache_clear()
    direct_d_lower.cache_clear()
    psi_polynomial_head_lower.cache_clear()
    lambda_grouped_lower.cache_clear()
    m.clear_large_caches()


@dataclass(slots=True)
class RuntimeCounters:
    clear_period: int
    interval_evaluations: int = 0
    cache_clears: int = 0
    next_clear: int = 0

    def __post_init__(self) -> None:
        self.next_clear = self.clear_period

    def note_interval_evaluation(self) -> None:
        self.interval_evaluations += 1
        if self.interval_evaluations >= self.next_clear:
            self.clear_caches()
            while self.next_clear <= self.interval_evaluations:
                self.next_clear += self.clear_period

    def clear_caches(self) -> None:
        clear_large_caches()
        gc.collect()
        self.cache_clears += 1


def split_axis(box: m.Box, axis: int) -> tuple[m.Box, m.Box]:
    depth = box.depth + 1
    if axis == 0:
        cut = (box.rl + box.rh) // 2
        assert box.rl < cut < box.rh
        return (
            m.Box(box.rl, cut, box.vl, box.vh, box.xl, box.xh, depth),
            m.Box(cut, box.rh, box.vl, box.vh, box.xl, box.xh, depth),
        )
    if axis == 1:
        cut = (box.vl + box.vh) // 2
        assert box.vl < cut < box.vh
        return (
            m.Box(box.rl, box.rh, box.vl, cut, box.xl, box.xh, depth),
            m.Box(box.rl, box.rh, cut, box.vh, box.xl, box.xh, depth),
        )
    assert axis == 2
    cut = (box.xl + box.xh) // 2
    assert box.xl < cut < box.xh
    return (
        m.Box(box.rl, box.rh, box.vl, box.vh, box.xl, cut, depth),
        m.Box(box.rl, box.rh, box.vl, box.vh, cut, box.xh, depth),
    )


def splittable_axes(box: m.Box) -> tuple[int, ...]:
    widths = (box.rh - box.rl, box.vh - box.vl, box.xh - box.xl)
    return tuple(axis for axis, width in enumerate(widths) if width >= 2)


def normalized_widths(box: m.Box, root_r_width: int) -> tuple[int, int, int]:
    return (
        (box.rh - box.rl) * (2 * q.ONE // 3) * (3 * q.ONE // 20),
        V_SENSITIVITY
        * (box.vh - box.vl)
        * root_r_width
        * (3 * q.ONE // 20),
        X_SENSITIVITY
        * (box.xh - box.xl)
        * root_r_width
        * (2 * q.ONE // 3),
    )


def choose_old_axis(box: m.Box, root_r_width: int) -> int | None:
    axes = splittable_axes(box)
    if not axes:
        return None
    widths = normalized_widths(box, root_r_width)
    return max(axes, key=widths.__getitem__)


def box_volume(box: m.Box) -> int:
    return (
        (box.rh - box.rl)
        * (box.vh - box.vl)
        * (box.xh - box.xl)
    )


def exact_fraction_text(numerator: int, denominator: int) -> str:
    value = Fraction(numerator, denominator)
    return f"{value.numerator}/{value.denominator}"


def make_root(rlo: int, rhi: int, region: Region) -> m.Box:
    return m.Box(
        rlo,
        rhi,
        parse_outward(region.vlo, upper=False),
        parse_outward(region.vhi, upper=True),
        parse_outward(region.xlo, upper=False),
        parse_outward(region.xhi, upper=True),
    )


class TraversalLimit(RuntimeError):
    pass


def progress_report(
    region_name: str,
    mode_name: str,
    counters: dict[str, int],
    stack_size: int,
    started: float,
) -> None:
    rss_raw, rss_mib = peak_rss()
    payload = {
        "event": "progress",
        "region": region_name,
        "mode": mode_name,
        "nodes": counters["nodes"],
        "primaryBoundEvaluations": counters["primaryBoundEvaluations"],
        "lookaheadBoundEvaluations": counters["lookaheadBoundEvaluations"],
        "groupedBoundEvaluations": counters["groupedBoundEvaluations"],
        "accepted": counters["accepted"],
        "discarded": counters["discarded"],
        "cutoffFrontier": counters["cutoffFrontier"],
        "stack": stack_size,
        "elapsedSeconds": monotonic() - started,
        "peakRssCounter": rss_raw,
        "peakRssMiB": rss_mib,
    }
    print(json.dumps(payload, sort_keys=True), file=sys.stderr, flush=True)


def evaluate_primary(
    box: m.Box,
    spec: ModeSpec,
    tail_n: int,
    d_terms: int,
    difference_modes: tuple[int, ...],
    use_physical_cap: bool,
    counters: dict[str, int],
    runtime: RuntimeCounters,
    *,
    lookahead: bool,
) -> PrimaryBound:
    if spec.primary_bound == "historical":
        lower, jhi = m.box_lower_bound(
            box, tail_n, difference_modes, use_physical_cap
        )
        result = PrimaryBound(lower, jhi, "historical-baseline")
    else:
        result = hybrid_box_lower_bound(
            box,
            tail_n,
            d_terms,
            difference_modes,
            use_physical_cap,
            use_direct_head=spec.primary_bound == "hybrid",
        )
        if result.source == "head":
            counters["headEvaluationWins"] += 1
        elif result.source == "tail":
            counters["tailEvaluationWins"] += 1

    counters["primaryBoundEvaluations"] += 1
    if lookahead:
        counters["lookaheadBoundEvaluations"] += 1
    runtime.note_interval_evaluation()
    return result


def choose_lookahead_axis(
    box: m.Box,
    spec: ModeSpec,
    tail_n: int,
    d_terms: int,
    grouped_head_n: int,
    difference_modes: tuple[int, ...],
    use_physical_cap: bool,
    counters: dict[str, int],
    runtime: RuntimeCounters,
    limit_reason,
) -> int | None:
    axes = splittable_axes(box)
    if not axes:
        return None

    best: tuple[tuple[int, int, int, int], int] | None = None
    for axis in axes:
        values: list[int] = []
        closed = 0
        for child in split_axis(box, axis):
            reason = limit_reason()
            if reason is not None:
                raise TraversalLimit(reason)
            result = evaluate_primary(
                child,
                spec,
                tail_n,
                d_terms,
                difference_modes,
                use_physical_cap,
                counters,
                runtime,
                lookahead=True,
            )
            if result.lower is None:
                closed += 1
                values.append(DISCARD_SENTINEL)
            else:
                child_lower = result.lower
                child_closed = result.direct_d_valid and child_lower >= 0
                if (
                    spec.lambda_lookahead_score
                    and result.direct_d_valid
                    and not child_closed
                ):
                    grouped_lower, grouped_reserve_lower = (
                        evaluate_lambda_grouped(
                            child,
                            grouped_head_n,
                            use_physical_cap,
                            counters,
                            runtime,
                        )
                    )
                    child_lower = max(child_lower, grouped_reserve_lower)
                    child_closed = grouped_lower >= 0
                if child_closed:
                    closed += 1
                values.append(child_lower)
        score = (closed, min(values), sum(values), -axis)
        candidate = (score, axis)
        if best is None or candidate[0] > best[0]:
            best = candidate
    assert best is not None
    return best[1]


def run_policy(
    root: m.Box,
    region_name: str,
    mode_name: str,
    cutoff_depth: int,
    case_node_limit: int,
    case_seconds: float,
    global_node_limit: int,
    global_nodes_before: int,
    global_deadline: float,
    root_r_width: int,
    tail_n: int,
    d_terms: int,
    grouped_head_n: int,
    difference_modes: tuple[int, ...],
    use_physical_cap: bool,
    report_period: int,
    runtime: RuntimeCounters,
) -> dict[str, object]:
    spec = MODES[mode_name]
    stack = [root]
    counters = {
        "nodes": 0,
        "primaryBoundEvaluations": 0,
        "lookaheadBoundEvaluations": 0,
        "groupedBoundEvaluations": 0,
        "accepted": 0,
        "discarded": 0,
        "acceptedByHistoricalBaseline": 0,
        "acceptedByDirectDTail": 0,
        "acceptedByDirectDHead": 0,
        "acceptedByLambdaGrouped": 0,
        "headEvaluationWins": 0,
        "tailEvaluationWins": 0,
        "invalidDirectD": 0,
        "cutoffFrontier": 0,
        "unsplittableFrontier": 0,
    }
    split_axes = [0, 0, 0]
    frontier_volume = 0
    max_depth = root.depth
    stack_peak = 1
    reason = "complete"
    started = monotonic()
    case_deadline = min(global_deadline, started + case_seconds)
    cache_clears_before = runtime.cache_clears

    def limit_reason() -> str | None:
        if global_nodes_before + counters["nodes"] >= global_node_limit:
            return "global-max-nodes"
        if counters["nodes"] >= case_node_limit:
            return "allocated-max-nodes"
        now = monotonic()
        if now >= global_deadline:
            return "global-max-seconds"
        if now >= case_deadline:
            return "allocated-max-seconds"
        return None

    progress_report(region_name, mode_name, counters, len(stack), started)
    next_report = report_period
    while stack:
        if counters["nodes"] >= next_report:
            progress_report(
                region_name, mode_name, counters, len(stack), started
            )
            while next_report <= counters["nodes"]:
                next_report += report_period
        if counters["nodes"] >= case_node_limit:
            reason = "allocated-max-nodes"
            break
        current_limit = limit_reason()
        if current_limit is not None:
            reason = current_limit
            break

        box = stack.pop()
        counters["nodes"] += 1
        max_depth = max(max_depth, box.depth)
        primary = evaluate_primary(
            box,
            spec,
            tail_n,
            d_terms,
            difference_modes,
            use_physical_cap,
            counters,
            runtime,
            lookahead=False,
        )
        if primary.lower is None:
            counters["discarded"] += 1
            continue
        if not primary.direct_d_valid:
            counters["invalidDirectD"] += 1
        elif primary.lower >= 0:
            counters["accepted"] += 1
            if primary.source == "historical-baseline":
                counters["acceptedByHistoricalBaseline"] += 1
            elif primary.source == "head":
                counters["acceptedByDirectDHead"] += 1
            else:
                counters["acceptedByDirectDTail"] += 1
            continue

        current_limit = limit_reason()
        if current_limit is not None:
            stack.append(box)
            reason = current_limit
            break

        if spec.lambda_grouped and primary.direct_d_valid:
            grouped_lower, _grouped_reserve_lower = evaluate_lambda_grouped(
                box,
                grouped_head_n,
                use_physical_cap,
                counters,
                runtime,
            )
            if grouped_lower >= 0:
                counters["accepted"] += 1
                counters["acceptedByLambdaGrouped"] += 1
                continue

        if box.depth >= cutoff_depth:
            counters["cutoffFrontier"] += 1
            frontier_volume += box_volume(box)
            continue

        current_limit = limit_reason()
        if current_limit is not None:
            stack.append(box)
            reason = current_limit
            break

        try:
            if spec.split_policy == "lookahead":
                axis = choose_lookahead_axis(
                    box,
                    spec,
                    tail_n,
                    d_terms,
                    grouped_head_n,
                    difference_modes,
                    use_physical_cap,
                    counters,
                    runtime,
                    limit_reason,
                )
            else:
                axis = choose_old_axis(box, root_r_width)
        except TraversalLimit as exc:
            stack.append(box)
            reason = str(exc)
            break

        if axis is None:
            counters["unsplittableFrontier"] += 1
            frontier_volume += box_volume(box)
            continue
        split_axes[axis] += 1
        left, right = split_axis(box, axis)
        stack.append(right)
        stack.append(left)
        stack_peak = max(stack_peak, len(stack))
        max_depth = max(max_depth, left.depth)

    unresolved_stack = len(stack)
    if stack:
        frontier_volume += sum(box_volume(box) for box in stack)
    if reason == "complete":
        if counters["cutoffFrontier"]:
            reason = "cutoff-depth"
        elif counters["unsplittableFrontier"]:
            reason = "unsplittable-dyadic-box"

    root_volume = box_volume(root)
    elapsed = monotonic() - started
    rss_raw, rss_mib = peak_rss()
    progress_report(region_name, mode_name, counters, len(stack), started)
    return {
        "region": region_name,
        "mode": mode_name,
        **counters,
        "stopReason": reason,
        "unresolvedStack": unresolved_stack,
        "frontier": (
            counters["cutoffFrontier"]
            + counters["unsplittableFrontier"]
            + unresolved_stack
        ),
        "maxDepth": max_depth,
        "stackPeak": stack_peak,
        "splitAxes": dict(zip(AXIS_NAMES, split_axes, strict=True)),
        "frontierVolumeFraction": exact_fraction_text(
            frontier_volume, root_volume
        ),
        "frontierVolumeFractionFloat": frontier_volume / root_volume,
        "allocatedMaxNodes": case_node_limit,
        "allocatedMaxSeconds": case_seconds,
        "elapsedSeconds": elapsed,
        "cacheClears": runtime.cache_clears - cache_clears_before,
        "peakRssCounter": rss_raw,
        "peakRssMiB": rss_mib,
    }


def comma_list(text: str) -> tuple[str, ...]:
    return tuple(part.strip() for part in text.split(",") if part.strip())


def unique(items: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(items))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rlo", default=RLO)
    parser.add_argument("--rhi", default=RHI)
    parser.add_argument(
        "--regions",
        default=",".join(DEFAULT_REGIONS),
        help=(
            "comma-separated subset of full-slab,adjacent-high,extreme-high"
        ),
    )
    parser.add_argument(
        "--modes",
        default=",".join(DEFAULT_MODES),
        help=(
            "comma-separated subset of historical-baseline,"
            "tail-directd-old,hybrid-old,hybrid-lookahead,"
            "hybrid-lambda-old,hybrid-lookahead-lambda-close,"
            "hybrid-lambda-lookahead"
        ),
    )
    parser.add_argument(
        "--include-historical-baseline",
        action="store_true",
        help="append the non-controlled historical full-D comparison",
    )
    parser.add_argument(
        "--include-lambda-grouped",
        action="store_true",
        help="append the optional hybrid-lambda-old comparison",
    )
    parser.add_argument(
        "--include-lambda-lookahead",
        action="store_true",
        help="append the exploratory hybrid-lambda-lookahead comparison",
    )
    parser.add_argument(
        "--include-lambda-close",
        action="store_true",
        help=(
            "append primary-lookahead topology with lambda used only for "
            "leaf closure"
        ),
    )
    parser.add_argument("--tail", type=int, default=TAIL_N)
    parser.add_argument("--d-terms", type=int, default=D_TERMS)
    parser.add_argument("--group-head", type=int, default=TAIL_N)
    parser.add_argument("--cutoff-depth", type=int, default=14)
    parser.add_argument(
        "--max-nodes",
        type=int,
        default=200_000,
        help="global visited-node budget, shared equally across all runs",
    )
    parser.add_argument(
        "--max-seconds",
        type=float,
        default=120.0,
        help="global traversal-time budget, shared equally across all runs",
    )
    parser.add_argument("--cache-clear-period", type=int, default=5_000)
    parser.add_argument("--report-period", type=int, default=1_000)
    parser.add_argument(
        "--physical-cap",
        action="store_true",
        help=(
            "use the J-dependent shape cap (sound experiment, but not "
            "fidelity to the formal DirectD leaf checker)"
        ),
    )
    args = parser.parse_args()

    regions = unique(comma_list(args.regions))
    modes = unique(comma_list(args.modes))
    if args.include_historical_baseline and "historical-baseline" not in modes:
        modes += ("historical-baseline",)
    if args.include_lambda_grouped and "hybrid-lambda-old" not in modes:
        modes += ("hybrid-lambda-old",)
    if (
        args.include_lambda_lookahead
        and "hybrid-lambda-lookahead" not in modes
    ):
        modes += ("hybrid-lambda-lookahead",)
    if (
        args.include_lambda_close
        and "hybrid-lookahead-lambda-close" not in modes
    ):
        modes += ("hybrid-lookahead-lambda-close",)
    if not regions or any(name not in REGIONS for name in regions):
        parser.error("--regions contains an unknown or empty region")
    if not modes or any(name not in MODES for name in modes):
        parser.error("--modes contains an unknown or empty mode")
    if args.tail < 2 or args.d_terms < 1 or args.group_head < 1:
        parser.error(
            "--tail must be >=2 and --d-terms/--group-head must be >=1"
        )
    if args.cutoff_depth < 0:
        parser.error("--cutoff-depth must be nonnegative")
    if (
        args.max_nodes <= 0
        or not math.isfinite(args.max_seconds)
        or args.max_seconds <= 0
    ):
        parser.error("resource budgets must be positive")
    if args.cache_clear_period <= 0 or args.report_period <= 0:
        parser.error("cache/report periods must be positive")

    rlo = parse_outward(args.rlo, upper=False)
    rhi = parse_outward(args.rhi, upper=True)
    if not 0 < rlo < rhi < q.ONE:
        parser.error("the outward-rounded R slab must satisfy 0<rlo<rhi<1")

    run_specs = tuple((region, mode) for region in regions for mode in modes)
    if args.max_nodes < len(run_specs):
        parser.error("--max-nodes must allocate at least one node per run")
    case_node_limit = args.max_nodes // len(run_specs)
    case_seconds = args.max_seconds / len(run_specs)
    physical_cap = args.physical_cap
    root_r_width = rhi - rlo
    difference_modes = m.weight_difference_modes(rlo, rhi, args.tail)
    runtime = RuntimeCounters(args.cache_clear_period)

    engine_paths = (
        PROJECT_ROOT / "verify_lr_compact_R34_V_interval.py",
        PROJECT_ROOT / "verify_lr_midcompact_V_interval.py",
    )
    reference_paths = (
        LEAN_ROOT / ".lake/scratch/experiment_compact_v_direct_head.py",
        LEAN_ROOT / ".lake/scratch/experiment_compact_v_lambda_grouped.py",
        LEAN_ROOT / "scripts/benchmark_compact_v_split_policy.py",
        LEAN_ROOT
        / "InformationTheory/CourtadeKumar/LRCompactVDirectD.lean",
        LEAN_ROOT
        / (
            "InformationTheory/CourtadeKumar/"
            "LRCompactVHybridDirectDLeafChecker.lean"
        ),
    )
    roots = {
        name: make_root(rlo, rhi, REGIONS[name]) for name in regions
    }
    invalid_roots = [
        name for name, root in roots.items() if not direct_d_valid(root)
    ]
    if invalid_roots:
        parser.error(
            "DirectDValid failed (requires rhi<1 and vlo^2*xlo<1) for: "
            + ",".join(invalid_roots)
        )
    output: dict[str, object] = {
        "schema": "compact-v-combined-reductions-benchmark-v2",
        "precision": q.PREC,
        "tailN": args.tail,
        "directDTerms": args.d_terms,
        "groupHeadN": args.group_head,
        "physicalCap": physical_cap,
        "checkerFidelity": (
            "non-fidelity physical-cap experiment"
            if physical_cap
            else "DirectD/Psi acceptance predicate"
        ),
        "arithmeticFidelity": (
            "Q132 predictor; P-tail/W enclosure is not bit-for-bit Lean's "
            "exact-rational certificate arithmetic"
        ),
        "regions": list(regions),
        "roots": {
            name: {
                "R": [root.rl, root.rh],
                "v": [root.vl, root.vh],
                "x": [root.xl, root.xh],
            }
            for name, root in roots.items()
        },
        "modes": list(modes),
        "cutoffDepth": args.cutoff_depth,
        "limits": {
            "globalMaxNodes": args.max_nodes,
            "globalMaxSeconds": args.max_seconds,
            "runs": len(run_specs),
            "allocatedNodesPerRun": case_node_limit,
            "allocatedSecondsPerRun": case_seconds,
            "cacheClearPeriodEvaluations": args.cache_clear_period,
            "reportPeriodNodes": args.report_period,
        },
        "predicates": {
            "discard": "J_upper <= 0",
            "historicalBaselineAccept": (
                "historical full sign-safe L_V lower >= 0"
            ),
            "tailDirectDAccept": (
                "DirectDValid and tail-only checker-shaped L_V lower >= 0"
            ),
            "hybridAccept": "DirectDValid and checker-shaped L_V lower >= 0",
            "lambdaGroupedAccept": "S_lower(Q + lambda*C) >= 0",
            "lambdaLookaheadReserveLower": (
                "B_lower*S_lower if S_lower>=0, else B_upper*S_lower"
            ),
            "lambdaCloseTopology": (
                "primary lookahead score; lambda evaluated only at current box"
            ),
            "lookaheadScore": [
                "immediately_closed_children",
                "minimum_child_lower",
                "sum_child_lowers",
                "negative_axis_number",
            ],
        },
        "measurementCaveats": {
            "historicalBaselineControlled": False,
            "lookaheadWinCountersIncludeSpeculativeChildren": True,
            "peakRssIsProcessCumulative": True,
            "lateRunMayLoseTimeToGlobalDeadlineOverhead": True,
        },
        "sourceSha256": {
            path.name: source_sha256(path)
            for path in (
                *engine_paths,
                Path(__file__).resolve(),
            )
        },
        "referenceSourceSha256": {
            path.name: source_sha256(path)
            for path in reference_paths
            if path.is_file()
        },
        "results": [],
    }

    global_started = monotonic()
    global_deadline = global_started + args.max_seconds
    global_nodes = 0
    results = output["results"]
    assert isinstance(results, list)
    for region_name, mode_name in run_specs:
        root = roots[region_name]
        result = run_policy(
            root,
            region_name,
            mode_name,
            args.cutoff_depth,
            case_node_limit,
            case_seconds,
            args.max_nodes,
            global_nodes,
            global_deadline,
            root_r_width,
            args.tail,
            args.d_terms,
            args.group_head,
            difference_modes,
            physical_cap,
            args.report_period,
            runtime,
        )
        results.append(result)
        nodes = result["nodes"]
        assert isinstance(nodes, int)
        global_nodes += nodes
        runtime.clear_caches()

    rss_raw, rss_mib = peak_rss()
    output["summary"] = {
        "nodes": global_nodes,
        "intervalEvaluations": runtime.interval_evaluations,
        "cacheClears": runtime.cache_clears,
        "elapsedSeconds": monotonic() - global_started,
        "peakRssCounter": rss_raw,
        "peakRssMiB": rss_mib,
    }
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
