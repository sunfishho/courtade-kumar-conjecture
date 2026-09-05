# Natural-interval production pilot

Entry point: `InformationTheory.CourtadeKumar.NaturalPilot.Certificate`.

The theorem
`CourtadeKumar.RootRatioNaturalProductionPilot.certificate_sound`
proves the actual production predicate `LRDeterminantFirstBracketAt p`
from membership in `RootRatioNaturalProductionPilot.pilotBox` alone:

- s = 1/16;
- 767/256 <= k <= 769/256;
- 767/2048 <= chi <= 769/2048.

`center_mem_box` proves that the box is nonempty. The stronger theorem
`production_firstBracket_positive` proves strict positivity.

## Verification and scope

All 14 modules here and the 12 changed/shared numerical prerequisites and
scalar core were source-compiled serially against the existing Lean 4.28.0 /
Mathlib build. The final production axiom audit is exactly
`propext, Classical.choice, Quot.sound`. There are no native/VM proof
shortcuts, additional axioms, or remaining numerical certificate premises.

The critical improvement is the interval evaluation identity
Y = 1 + 1/k - s. Its sharper D1 bound allows direct natural Cbase/Psi
enclosures without corner-monotonicity proofs or further subdivision.
The rigorous lower margin is 21550625417/70368744177664.

This is ONE strict subbox of base-face-030. It is not a cover of the whole
parent box, the full base-face region, fixed16, or a proof of CK.

## Production definition refactor

Twenty unchanged production definitions now live in
`LRDeterminantScalarTargetCore.lean`; their old analytic modules import it.
Run `python3 scripts/check_lr_scalar_target_relocation.py` to check their
declaration text against the preceding checkpoint. The check passes for all
twenty names. This check supplements, and does not replace, Lean verification.

The old large analytic modules were not rebuilt as a group. Their caches may
predate this relocation. Do not combine the new modules with stale cached
copies that still declare these same constants; let Lake rebuild the affected
dependency branch when using those analytic modules.

## Targeted build

Build the module target
`InformationTheory.CourtadeKumar.NaturalPilot.Certificate`, not the whole
InformationTheory root. Reuse the compatible Mathlib build. On a constrained
host, compile the dependency closure sequentially, with one Lean worker and
a host-memory guard. The latest local checks kept the existing 6 GB Lean
allocation cap and stopped below 42% memory availability.

The earlier scratch/checkpoint copies are historical snapshots; this directory
is now the authoritative source for the completed pilot.
