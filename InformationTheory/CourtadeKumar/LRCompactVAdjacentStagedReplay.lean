import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Assembly

/-!
# Kernel-checked adjacent compact-`V` replay

Stable public wrapper around the segmented generated certificate for

`R ∈ [921/1024, 9/10]`, `v ∈ [15/16, 31/32]`, and
`x ∈ [63/64, 127/128]`.
-/

set_option autoImplicit false

namespace CourtadeKumar

abbrev lrCompactVAdjacentStagedReplayBox : CertificateBox :=
  GeneratedLRCompactVAdjacentStagedReplayV1.rootBox

theorem lrCompactVAdjacentStagedReplay_sound :
    ∀ point, lrCompactVAdjacentStagedReplayBox.Contains point →
      LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  GeneratedLRCompactVAdjacentStagedReplayV1.sound

end CourtadeKumar
