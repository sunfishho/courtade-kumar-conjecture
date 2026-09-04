import AgentRootRatioBaseFaceD1Standalone
import InformationTheory.CourtadeKumar.LRDeterminantD1

/-! Connect the independently checked small D1 enclosure to the existing
production definition. No full D9 evaluator or automatic payload is needed. -/

set_option autoImplicit false

namespace CourtadeKumar.RootRatioBaseFaceD1Standalone

open RationalEnclosure RootRatioBaseFaceRoundedPilot

theorem production_rounded_contains {p : CertificatePoint}
    (hs : p.s = 1 / 16)
    (hk : (767 / 256 : ℝ) ≤ p.k ∧ p.k ≤ 769 / 256) :
    pilot8Bounds.d1.Contains (lrDeterminantD1 p) := by
  have hs0 : p.s ≠ 0 := by rw [hs]; norm_num
  have hkpos : 0 < p.k := lt_of_lt_of_le (by norm_num) hk.1
  have hy : lrDeterminantY p = (1 + p.k - p.s * p.k) / p.k := by
    unfold lrDeterminantY lrCertificateB lrCertificateE
    field_simp [hs0, hkpos.ne']
    <;> ring
  have hsI : sI.Contains p.s := by norm_num [sI, point, Contains, hs]
  have hkI : kI.Contains p.k := by simpa [kI, Contains] using hk
  simpa only [d1Value, lrDeterminantD1, hy] using rounded_contains hsI hkI

theorem production_positive {p : CertificatePoint}
    (hs : p.s = 1 / 16)
    (hk : (767 / 256 : ℝ) ≤ p.k ∧ p.k ≤ 769 / 256) :
    0 < lrDeterminantD1 p := by
  have h := (production_rounded_contains hs hk).1
  have hlo : (0 : ℝ) < (pilot8Bounds.d1.lower : ℝ) := by
    norm_num [pilot8Bounds]
  exact hlo.trans_le h

#print axioms CourtadeKumar.RootRatioBaseFaceD1Standalone.production_rounded_contains
#print axioms CourtadeKumar.RootRatioBaseFaceD1Standalone.production_positive

end CourtadeKumar.RootRatioBaseFaceD1Standalone
