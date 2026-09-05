# Numerical certificate source checkpoint — 2026-09-04

This is an explicit work-in-progress source snapshot, not a complete CK proof
or a standalone clean-checkout build. It preserves the latest numerical work
from the local scratch directory without including unrelated working-tree
changes, generated binaries, or exercise deletions.

## Verified locally

Using Lean 4.28.0 and the existing local Mathlib/project build:

- AgentRootRatioPrimitiveNumericalPilot: four logarithm enclosures at the
  actual first ordinary-box centers, proved using eight exact series terms.
- AgentRootRatioQNumericalPilot: three square-root enclosures plus Q and Q'
  enclosures at the first ordinary-box center.
- AgentRootRatioNumericalPilotAxiomAudit: all nine exported bounds depend
  only on propext, Classical.choice, and Quot.sound.
- AgentRootRatioBaseFaceDominanceArithmetic: the short literal rational
  sign/dominance comparison, with the same clean axiom audit.

There is no native_decide, VM proof evaluator, sorry, or added axiom in these
new proofs. The audit does not establish that every local imported source is
identical to the source of its cached build.

## Pending

All other Lean files here are uncompiled drafts. In particular, the base-face
pilot is NOT a proved box: its five payload receipts, four interval-cover
receipts, and semantic assembly remain to be checked. The literal dominance
proof alone does not prove that its intervals enclose production values.

The proposed box is s=1/16, k=[767/256,769/256],
chi=[767/2048,769/2048], a strict subbox of base-face-030, not its full cover.
Exact Python arithmetic prechecks passed for this subbox; those computations
are not Lean proofs.

The draft uses ordinary kernel-checked Boolean reduction for atomic receipts.
Large D9 imports reached the host-memory watchdog cutoff, so those attempts
were stopped and no successful replay is claimed.

## Build context and limitations

Sources retain their scratch module names. To replay locally, put a build
directory for these module names on LEAN_PATH after the compatible project
build and before external dependencies, then compile imports in order.
Do not initiate a whole-project rebuild on a memory-constrained host.

Additional local dependencies are not bundled: the current project interval
library, AgentConcreteRootRatioCalculus for the semantic wrapper, and the
compatible Mathlib build. The working project has uncommitted dependency
changes; this checkpoint intentionally does not claim fresh-clone
reproducibility. D9 evaluator source is newer than its cached olean, and the
draft wrapper includes the missing short comparison lemma locally.

Full fixed16 and CK remain unproved unconditionally. Continue with the
small numerical receipt path and then connect it to the semantic assembly.

## Continuation: smaller B and D1 proof path

Three additional modules have now compiled, serially with the memory guard:

- AgentRootRatioBaseFaceD1Standalone: 4.2 seconds, minimum observed
  memory availability 47%. Proves the exact rounded D1 interval cover
  and real containment throughout the specified s/k interval.
- AgentRootRatioBaseFaceBStandalone: 9.1 seconds, minimum 47%.
  Proves the exact rounded B interval cover, including literal square-root
  and logarithm certificate checks, and real containment throughout the
  specified s/k/chi box.
- AgentRootRatioBaseFaceTwoBoundsAssembly: 2.0 seconds, minimum 48%.
  Uses those two proved bounds to establish the scalar first-bracket
  inequality conditional ONLY on Cbase and Psi interval containments.

All printed exported proof audits use exactly propext, Classical.choice,
and Quot.sound. These modules avoid full D9 evaluator imports and automatic
payload generation. Finite checks use ordinary norm_num; the assembly uses
ordinary nlinarith. No native or VM proof shortcut was introduced.

These three are exceptions to the earlier uncompiled-draft inventory.
The original heavy payload/cover receipt modules remain uncompiled.
The standalone theorems concern explicit real formulas matching the D1
and B formulas; they do not yet prove the old automatic-evaluator cover
predicates definitionally equal to these new checks.

AgentRootRatioBaseFaceD1Production and AgentRootRatioBaseFaceBProduction
are UNCOMPILED bridge drafts. Both import attempts were stopped at 41%
memory availability, below the unchanged 42% cutoff. Do not claim their
production-named conclusions, a complete base-face box, or CK from this
checkpoint. The Cbase/Psi bounds and production identification remain open.

Replay the small files after the original DominanceArithmetic module,
in the three-module order above. Stop rather than retry large production
imports while memory is constrained.

## Direct natural-interval pilot: numerical hypotheses closed

The latest continuation supersedes the earlier missing Cbase/Psi numerical
bounds for this ONE pilot. A new small-import path proves a strictly positive
first bracket on the SAME depth-eight box, without extra subdivision and
without corner-monotonicity premises:

`CourtadeKumar.RootRatioNaturalPilotAssembly.pilot_positive`.

Its only hypotheses are the displayed k/chi interval membership conditions;
s is exactly 1/16. It concerns the explicit scalar formulas defined in the
new small modules. The production-name integration is STILL outstanding,
and this is NOT the full base-face region, fixed16, or CK.

The successful change was algebraic: evaluate D1 using
Y = 1 + 1/k - s instead of evaluating (1+k-sk)/k with repeated occurrences
of the interval k. The tighter D1 bound makes direct natural interval Cbase
and Psi bounds sufficient. This eliminates the need for the former heavy
corner-payload path for this pilot.

All ten new Lean modules compiled serially with the unchanged memory guard:

| Module suffix (AgentRootRatio prefix) | Seconds | Minimum availability |
| --- | ---: | ---: |
| NaturalQSound | 12.5 | 45% |
| NaturalQS | 7.1 | 46% |
| NaturalQE | 7.0 | 50% |
| NaturalQY | 3.3 | 50% |
| NaturalQBe | 8.7 | 55% |
| NaturalQBy | 11.9 | 47% |
| NaturalGeometry | 5.7 | 48% |
| BaseFaceD1Sharp | 4.3 | 45% |
| NaturalComponents | 6.1 | 43% |
| NaturalPilotAssembly | 2.7 | 49% |

The soundness theorem checks Q and Q' over entire input intervals, not just
their midpoints. Five independent literal square-root/log receipts give
24-bit rounded primitive intervals. Geometry and the two final component
covers are checked separately, keeping intermediate rational expressions
short. The final assembly audit is exactly propext, Classical.choice,
Quot.sound. No sorry, extra axiom, native evaluator, or VM proof shortcut.

The final rigorous rational lower margin is
21550625417/70368744177664 > 0. The older D1 bound would instead give
-3033779765/140737488355328 on these same natural Cbase/Psi bounds.

AgentRootRatioNaturalBasePrecheck.py test verifies the exact literal bounds
and both margin signs with Fractions before Lean. The script depends on
the local historical arithmetic mirror; it is not itself a proof or a
standalone fresh-clone utility. Its default diagnostic mode compares against
the OLD narrow Cbase bounds and therefore reports some failures; the new
route deliberately uses wider Cbase bounds with sharper D1 instead.

Next: integrate the explicit formulas with production definitions, then
apply the cheaper mechanism to the rest of the required box cover.
