import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Certificate

/-!
# Kernel-checked adjacent compact-`V` replay

Stable public wrapper around the eight-terminal centered-monotone certificate for

`R ∈ [921/1024, 9/10]`, `v ∈ [15/16, 31/32]`, and
`x ∈ [63/64, 127/128]`.
-/

set_option autoImplicit false

namespace CourtadeKumar

abbrev lrCompactVAdjacentStagedReplayBox : CertificateBox :=
  GeneratedLRCompactVCenteredMonotoneV1.rootBox

theorem lrCompactVAdjacentStagedReplay_sound :
    ∀ point, lrCompactVAdjacentStagedReplayBox.Contains point →
      LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  GeneratedLRCompactVCenteredMonotoneV1.target_nonnegative

end CourtadeKumar
