import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantRadial

/-! Retain the positive correction which pays the adverse B-weighted change. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

lemma delta_reserve_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrCertificateE p / 4 * ((1 - p.chi) * (1 - lrCertificateE p / 2) + 12 * p.chi / 7) ≤
      lrDeterminantDelta p - lrLowRatioBWeight p * lrCertificateE p / 4 := by
  let v := lrCertificateV p
  let x := lrCertificateX p
  let e := lrCertificateE p
  let d := 1 - v
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hvLo : (3 / 4 : ℝ) ≤ v := LRAnalyticMidpoint.v_lower hi hs hk
  have he : e ∈ Ioo (0 : ℝ) 1 := hi.2.1
  have hc : p.chi ∈ Ioo (0 : ℝ) 1 := hi.2.2
  have hd : 0 ≤ d := sub_nonneg.mpr hv.2.le
  have hx : 0 < x := by
    dsimp [x, lrCertificateX]
    nlinarith [mul_lt_mul_of_pos_right hc.2 he.1, he.2]
  have hx1 : x ≤ 1 := sub_le_self _ (mul_nonneg hc.1.le he.1.le)
  have hvSq : v ^ 2 * x = 1 - e := by
    have h := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr he.2.le) hx.le)
    change v ^ 2 = (1 - e) / x at h
    exact (eq_div_iff hx.ne').mp h
  have hgeom : e * (1 - p.chi) ≤ d * (1 + v) := by
    have hvSq1 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hm := mul_le_mul_of_nonneg_right hx1 (sub_nonneg.mpr hvSq1)
    have hxE : x = 1 - p.chi * e := rfl
    dsimp [d]
    nlinarith
  have hlow : e * (1 - p.chi) / 4 ≤ d / (1 + v) := by
    rw [le_div_iff₀ (by linarith [hv.1] : 0 < 1 + v)]
    have hm := mul_le_mul_of_nonneg_right hgeom (by linarith [hv.1] : 0 ≤ 1 + v)
    have hsq : (1 + v) ^ 2 ≤ 4 := by nlinarith [hv.1, hv.2]
    have hm2 := mul_le_mul_of_nonneg_left hsq hd
    nlinarith
  have hm : (3 / 7 : ℝ) ≤ v / (1 + v) := by
    rw [le_div_iff₀ (by linarith [hv.1] : 0 < 1 + v)]
    linarith
  have h1 := mul_le_mul_of_nonneg_right hlow (show 0 ≤ 1 - e / 2 by linarith [he.2])
  have h2 := mul_le_mul_of_nonneg_right hm (mul_nonneg hc.1.le he.1.le)
  have hid : lrDeterminantDelta p - lrLowRatioBWeight p * e / 4 =
      d / (1 + v) * (1 - e / 2) + v / (1 + v) * (p.chi * e) := by
    rw [(lrLowRatio_weight_identities hi).2.1]
    unfold lrDeterminantDelta
    change (1 - v * x) / (1 + v) - 2 * d / (1 + v) * e / 4 = _
    have hxE : x = 1 - p.chi * e := rfl
    rw [hxE]
    dsimp [d]
    field_simp [show 1 + v ≠ 0 by linarith [hv.1]]
    ring
  change e / 4 * ((1 - p.chi) * (1 - e / 2) + 12 * p.chi / 7) ≤ _
  rw [hid]
  nlinarith

end CourtadeKumar.LRAnalyticDeterminant
