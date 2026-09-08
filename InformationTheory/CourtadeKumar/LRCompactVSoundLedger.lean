import InformationTheory.CourtadeKumar.LRCompactVCorrelatedGeneratedCertificate

/-!
# Abstract compact-`V` soundness through `R = 9/10`

Downstream analytic assembly uses only the pointwise nonnegativity consequence
of the compact certificate family.  It does not depend on the identity of a
particular deterministic generator or on the representation of its replay
data.  This structure records exactly that mathematical interface.
-/

namespace CourtadeKumar

structure LRCompactVSoundLedger : Prop where
  v_nonnegative :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 → R ≤ 9 / 10 →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      0 ≤ lrLowVReserve R v t

end CourtadeKumar
