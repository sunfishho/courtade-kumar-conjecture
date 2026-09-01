#!/usr/bin/env python3
"""Bounded split-policy canaries for the audited Compact-V evaluator.

This script never runs Lean and does not generate a certificate.  It reuses
the exact integer interval evaluator from ``verify_lr_midcompact_V_interval``
and compares topology policies on a named root or subbox.  The default depth
cutoff makes every default run deterministic and small.

The successful one-step policy is ``lookahead-close``.  For every unresolved
box it evaluates the two midpoint children on each axis and maximizes

    (number of immediately closed children,
     minimum child lower bound,
     sum of child lower bounds,
     -axis_number).

A rigorous J<=0 discard is represented by the fixed sentinel 10**100 in the
last two fields.  Axis numbers are R=0, v=1, x=2, so exact ties prefer R, then
v, then x.  Lookahead affects only topology selection; every terminal is
still accepted by the unchanged audited interval predicate.

Examples (run from the project root):

  python3 lean-formalization/scripts/benchmark_compact_v_split_policy.py
  python3 lean-formalization/scripts/benchmark_compact_v_split_policy.py \
      --region full-slab --cutoff-depth 14 --modes baseline,no-r,lookahead-close
  python3 lean-formalization/scripts/benchmark_compact_v_split_policy.py \
      --region adjacent-high --complete --max-seconds 120 --max-nodes 200000
"""

from __future__ import annotations

import argparse
import gc
import hashlib
import json
import resource
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from time import monotonic


PROJECT_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PROJECT_ROOT))

import verify_lr_compact_R34_V_interval as q  # noqa: E402
import verify_lr_midcompact_V_interval as m  # noqa: E402


RLO = "921/1024"
RHI = "9/10"
TAIL_N = 64
V_SENSITIVITY = 16
X_SENSITIVITY = 8
DISCARD_SENTINEL = 10**100
AXIS_NAMES = ("R", "v", "x")


@dataclass(frozen=True, slots=True)
class Region:
    vlo: str
    vhi: str
    xlo: str
    xhi: str


REGIONS = {
    # The deterministic canary on which lookahead-close reduced 45,376
    # audited-policy leaves to 1,387 leaves.
    "adjacent-high": Region("15/16", "31/32", "63/64", "127/128"),
    # Contains the narrow physical/J boundary and the audited depth-34 leaves.
    "extreme-high": Region("31/32", "1", "127/128", "1"),
    # A low-v, low-x control box.
    "low-corner": Region("1/3", "3/8", "17/20", "55/64"),
    # The whole hardest audited R slab.  Keep a cutoff for this region.
    "full-slab": Region("1/3", "1", "17/20", "1"),
}


def parse_outward(text: str, *, upper: bool) -> int:
    return m.parse_fraction(text, upper=upper)


def source_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def split_axis(box: m.Box, axis: int) -> tuple[m.Box, m.Box]:
    depth = box.depth + 1
    if axis == 0:
        cut = (box.rl + box.rh) // 2
        return (
            m.Box(box.rl, cut, box.vl, box.vh, box.xl, box.xh, depth),
            m.Box(cut, box.rh, box.vl, box.vh, box.xl, box.xh, depth),
        )
    if axis == 1:
        cut = (box.vl + box.vh) // 2
        return (
            m.Box(box.rl, box.rh, box.vl, cut, box.xl, box.xh, depth),
            m.Box(box.rl, box.rh, cut, box.vh, box.xl, box.xh, depth),
        )
    assert axis == 2
    cut = (box.xl + box.xh) // 2
    return (
        m.Box(box.rl, box.rh, box.vl, box.vh, box.xl, cut, depth),
        m.Box(box.rl, box.rh, box.vl, box.vh, cut, box.xh, depth),
    )


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


def choose_axis(
    box: m.Box,
    mode: str,
    root_r_width: int,
    difference_modes: tuple[int, ...],
    counters: dict[str, int],
) -> int:
    widths = normalized_widths(box, root_r_width)
    if mode == "baseline":
        return max(range(3), key=widths.__getitem__)
    if mode == "no-r":
        return max((1, 2), key=widths.__getitem__)
    assert mode == "lookahead-close"

    best: tuple[tuple[int, int, int, int], int] | None = None
    for axis in range(3):
        values: list[int] = []
        closed = 0
        for child in split_axis(box, axis):
            lower, _ = m.box_lower_bound(
                child, TAIL_N, difference_modes, True
            )
            counters["boundEvaluations"] += 1
            if lower is None:
                closed += 1
                values.append(DISCARD_SENTINEL)
            else:
                if lower > 0:
                    closed += 1
                values.append(lower)
        score = (closed, min(values), sum(values), -axis)
        candidate = (score, axis)
        if best is None or candidate[0] > best[0]:
            best = candidate
    assert best is not None
    return best[1]


def exact_fraction_text(numerator: int, denominator: int) -> str:
    value = Fraction(numerator, denominator)
    return f"{value.numerator}/{value.denominator}"


def run_policy(
    root: m.Box,
    mode: str,
    cutoff_depth: int | None,
    max_nodes: int,
    max_seconds: float,
    root_r_width: int,
    difference_modes: tuple[int, ...],
) -> dict[str, object]:
    stack = [root]
    counters = {
        "nodes": 0,
        "boundEvaluations": 0,
        "accepted": 0,
        "discarded": 0,
        "frontier": 0,
    }
    split_axes = [0, 0, 0]
    frontier_volume = 0
    max_depth = root.depth
    reason = "complete"
    started = monotonic()

    while stack:
        elapsed = monotonic() - started
        if counters["nodes"] >= max_nodes:
            reason = "max-nodes"
            break
        if elapsed >= max_seconds:
            reason = "max-seconds"
            break

        box = stack.pop()
        counters["nodes"] += 1
        lower, _ = m.box_lower_bound(box, TAIL_N, difference_modes, True)
        counters["boundEvaluations"] += 1
        if lower is None:
            counters["discarded"] += 1
            continue
        if lower > 0:
            counters["accepted"] += 1
            continue
        if cutoff_depth is not None and box.depth >= cutoff_depth:
            counters["frontier"] += 1
            frontier_volume += (
                (box.rh - box.rl)
                * (box.vh - box.vl)
                * (box.xh - box.xl)
            )
            continue

        axis = choose_axis(
            box, mode, root_r_width, difference_modes, counters
        )
        split_axes[axis] += 1
        left, right = split_axis(box, axis)
        stack.append(right)
        stack.append(left)
        max_depth = max(max_depth, left.depth)

    if stack:
        # Resource-limit exits leave these unresolved boxes plus any cutoff
        # frontier already counted above.
        counters["frontier"] += len(stack)
        frontier_volume += sum(
            (box.rh - box.rl)
            * (box.vh - box.vl)
            * (box.xh - box.xl)
            for box in stack
        )

    root_volume = (
        (root.rh - root.rl)
        * (root.vh - root.vl)
        * (root.xh - root.xl)
    )
    elapsed = monotonic() - started
    if reason == "complete" and counters["frontier"]:
        reason = "cutoff-depth"
    return {
        "mode": mode,
        **counters,
        "stopReason": reason,
        "maxDepth": max_depth,
        "splitAxes": dict(zip(AXIS_NAMES, split_axes, strict=True)),
        "frontierVolumeFraction": exact_fraction_text(
            frontier_volume, root_volume
        ),
        "frontierVolumeFractionFloat": frontier_volume / root_volume,
        "elapsedSeconds": elapsed,
        "maxRssCounter": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--region", choices=sorted(REGIONS), default="adjacent-high")
    parser.add_argument(
        "--modes",
        default="baseline,no-r,lookahead-close",
        help="comma-separated subset of baseline,no-r,lookahead-close",
    )
    parser.add_argument("--cutoff-depth", type=int, default=12)
    parser.add_argument(
        "--complete",
        action="store_true",
        help="remove the depth cutoff; resource bounds still apply",
    )
    parser.add_argument("--max-nodes", type=int, default=200_000)
    parser.add_argument("--max-seconds", type=float, default=120.0)
    args = parser.parse_args()

    requested_modes = args.modes.split(",")
    allowed_modes = {"baseline", "no-r", "lookahead-close"}
    assert requested_modes and all(mode in allowed_modes for mode in requested_modes)
    assert args.cutoff_depth >= 0
    assert args.max_nodes > 0
    assert args.max_seconds > 0

    rlo = parse_outward(RLO, upper=False)
    rhi = parse_outward(RHI, upper=True)
    region = REGIONS[args.region]
    root = m.Box(
        rlo,
        rhi,
        parse_outward(region.vlo, upper=False),
        parse_outward(region.vhi, upper=True),
        parse_outward(region.xlo, upper=False),
        parse_outward(region.xhi, upper=True),
    )
    root_r_width = rhi - rlo
    difference_modes = m.weight_difference_modes(rlo, rhi, TAIL_N)
    cutoff_depth = None if args.complete else args.cutoff_depth

    engine_paths = (
        PROJECT_ROOT / "verify_lr_compact_R34_V_interval.py",
        PROJECT_ROOT / "verify_lr_midcompact_V_interval.py",
    )
    output: dict[str, object] = {
        "schema": "compact-v-split-canary-v1",
        "region": args.region,
        "precision": q.PREC,
        "tailN": TAIL_N,
        "physicalCap": True,
        "root": {
            "R": [root.rl, root.rh],
            "v": [root.vl, root.vh],
            "x": [root.xl, root.xh],
        },
        "cutoffDepth": cutoff_depth,
        "maxNodes": args.max_nodes,
        "maxSeconds": args.max_seconds,
        "sourceSha256": {
            path.name: source_sha256(path) for path in engine_paths
        },
        "results": [],
    }
    results = output["results"]
    assert isinstance(results, list)
    for mode in requested_modes:
        results.append(
            run_policy(
                root,
                mode,
                cutoff_depth,
                args.max_nodes,
                args.max_seconds,
                root_r_width,
                difference_modes,
            )
        )
        m.clear_large_caches()
        gc.collect()

    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
