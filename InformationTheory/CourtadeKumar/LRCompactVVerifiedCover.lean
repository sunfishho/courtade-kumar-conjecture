import InformationTheory.CourtadeKumar.LRCompactVLowRReplay
import InformationTheory.CourtadeKumar.LRCompactVKernelPilot

/-!
# Explicit compact-V coverage available to the final assembly

The newly checked low-R rectangle and the earlier kernel pilot are both
removed from the residual ledger obligation. Their overlap needs no special
treatment: either soundness theorem suffices at an overlapping point.
-/

namespace CourtadeKumar

def lrCompactVVerifiedBoxes : List CertificateBox :=
  [lrCompactVLowRReplayBox, CompactVKernelPilot.box]

theorem lrCompactVVerifiedCover : LRCompactVPartialCover lrCompactVVerifiedBoxes := by
  intro box hbox
  simp only [lrCompactVVerifiedBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl
  · exact lrCompactVLowRReplay_sound
  · exact fun _ hpoint hphysical ↦ CompactVKernelPilot.certificate_sound hpoint hphysical

/-- The full compact-V premise now requires a proof only outside the two
explicitly listed, kernel-checked regions. -/
theorem lrCompactVSoundLedger_of_verifiedResidual
    (remaining : LRCompactVResidualLedger lrCompactVVerifiedBoxes) :
    LRCompactVSoundLedger :=
  LRCompactVSoundLedger.of_partialCover lrCompactVVerifiedCover remaining

end CourtadeKumar
