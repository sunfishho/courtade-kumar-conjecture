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
