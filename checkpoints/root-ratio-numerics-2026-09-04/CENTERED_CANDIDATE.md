# Centered base-face candidate — not a Lean certificate

The parent `base-face-030` is `s = 1/16`, `k ∈ [2,4]`,
`chi ∈ [1/4,1/2]`. The completed NaturalPilot theorem covers only a
strict subbox of this parent. This experiment does **not** upgrade that theorem.

## Reproduce

From the repository, run:

```sh
python3 -B scripts/experiment_lr_centered_base_face.py --smart --self-test --export
```

The script uses only the standard library and the tracked exact-log evaluator.
It is sequential, caps exploration at 2047 boxes, rounds interval operations
outward, and does not launch Lean or write files. Floats appear only in separate
diagnostics and the displayed approximate minimum, never in box acceptance.

Result: 287 box evaluations, 144 accepted candidate leaves, no pending boxes.
The exact minimum lower bound is positive (approximately `0.0000364806`).
The script checks total area and pairwise interior disjointness; the bisection
construction supplies the candidate cover. The adjacent JSON records all
144 rational boxes and their proposed lower bounds.

Nine independent direct-formula value checks and eighteen finite-difference
derivative diagnostics passed. These diagnostics are not proof checking.

## Why it helps

The evaluator uses a center value plus bounds for the two partial derivatives,
instead of enclosing all cancelling entropy values independently over a box.
It groups the common entropy terms before differentiation. The proposed rule is

`F(k,chi) ≥ F(center).lower − radiusK * abs(dK).upper − radiusChi * abs(dChi).upper`.

The splitting heuristic selects the larger derivative-radius contribution.
The first version used 164 leaves; endpoint interval multiplication plus the
new split rule uses 144. Endpoint monotonicity alone was insufficient to
make the direct-value approach comparably attractive on the sampled boxes.

## What Lean has checked

`LRDeterminantCenteredScalarCore.lean` proves the exact shared-expression
identities for production `Psi` and `Psi - G + 4*delta*W` using only the
lightweight scalar core. Fresh guarded source check: 4.4 seconds, minimum
observed available-memory reading 46%. Both theorem axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Still required before any parent-box theorem

1. Connect the interval derivative graph to production derivatives, reusing
   existing interval AD and mean-value soundness where possible.
2. Supply/check the primitive value and derivative enclosures. The experimental
   Q-prime derivative formula is `(2*t*QPrime(t)-1)/(4*t*(1-t))`; its link to
   the existing production Q-second theorem must be explicit.
3. Match arithmetic exactly: the new AD uses min/max of four endpoint products,
   not the older midpoint-radius multiplication. Every AD result is rounded
   outward to 32 bits; Q/QPrime primitive results use 24 bits, roots 20 bisections,
   logarithm normalization fuel 16, and eight log-series terms with tail bounds.
4. Kernel-check concrete bounds and the finite cover, then connect the parent
   box theorem to the boundary catalog. Start with one representative leaf to
   measure proof cost before generating a large replay.

The 144-leaf count says nothing yet about total Lean runtime or other parent
boxes. Fixed16 and CK remain unfinished. No whole-project rebuild was run.
