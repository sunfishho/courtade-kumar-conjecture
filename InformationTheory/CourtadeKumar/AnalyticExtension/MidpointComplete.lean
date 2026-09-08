import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCheckerSound
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalData
import InformationTheory.CourtadeKumar.AnalyticProgressClosure

/-! The entire remaining midpoint family is supplied by the analytic
reduction and its small kernel-checked rational certificate. -/
namespace CourtadeKumar.LRAnalyticMidpoint

/-- The complete upper-k logarithmic core, with no free certificate premise. -/
theorem upper_k_core : UpperKCoreCertificate := by
  intro p hi hr hkLo hk hsLo hs
  have hp : LRMidpointReducedCertificate.root.Contains p := by
    norm_num only [LRMidpointReducedCertificate.root, CertificateBox.Contains,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one]
    exact ⟨hsLo.le, hs.le, hkLo.le, hk, hi.2.2.1.le, hi.2.2.2.le⟩
  have h := subdivisionCertificate_sound
    (Relevant := fun _ => True)
    (Property := fun q => LRHighShapeInterior q → LRHighShapeVRelevant q → 0 ≤ coreTarget q)
    (acceptBox := LRMidpointReducedCertificate.Leaf.check)
    (discardBox := fun _ (_ : Unit) => false)
    LRMidpointReducedCertificate.Leaf.sound
    (by intro _ _ h; simp at h)
    LRMidpointReducedCertificate.certificate_checked p hp trivial
  exact h hi hr

theorem upper_k : UpperKCertificate := upper_k_of_core upper_k_core

/-- Inhabits the original compact midpoint interface used by the CK closure. -/
theorem midpoint :
    LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointCompactMidpointCoordinateTheorem :=
  midpoint_of_upper_k upper_k

end CourtadeKumar.LRAnalyticMidpoint
