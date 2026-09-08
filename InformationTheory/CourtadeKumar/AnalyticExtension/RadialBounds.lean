import InformationTheory.CourtadeKumar.LRDeterminantLowRatioSmallSAnalytic

/-! Sharper radial error bounds for the low-ratio analytic extension. -/
open Set
namespace CourtadeKumar.LRLowRatioAnalyticExtension

lemma v_near_one
    {point : CertificatePoint} (hi : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) (hs : point.s ≤ 1 / 16) :
    (99 / 100 : ℝ) ≤ lrCertificateV point := by
  have hd := lrLowRatio_one_sub_v_le_e hi
  have he := lrLowRatioE_le_s_sq hi hregion
  have hs0 := hi.1.1.le
  have hsSq : point.s ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by nlinarith
  nlinarith

lemma v_one_half_le
    {point : CertificatePoint} (hi : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) (hs : point.s ≤ 1 / 16) :
    (1 / 2 : ℝ) ≤ lrCertificateV point := by
  linarith [v_near_one hi hregion hs]

lemma one_sub_v_sq_le_e
    {point : CertificatePoint} (hi : LRHighShapeInterior point) :
    1 - lrCertificateV point ^ 2 ≤ lrCertificateE point := by
  let e := lrCertificateE point
  let x := lrCertificateX point
  have he : e ∈ Ioo (0 : ℝ) 1 := hi.2.1
  have hxPos : 0 < x := by
    dsimp [x, lrCertificateX]
    have hprod : point.chi * e < 1 :=
      (mul_lt_mul_of_pos_right hi.2.2.2 he.1).trans_le (by simpa using he.2.le)
    linarith
  have hxLe : x ≤ 1 := by
    dsimp [x, lrCertificateX]
    exact sub_le_self _ (mul_nonneg hi.2.2.1.le he.1.le)
  have hradPos : 0 ≤ (1 - e) / x :=
    div_nonneg (sub_nonneg.mpr he.2.le) hxPos.le
  have hvSq : lrCertificateV point ^ 2 = (1 - e) / x := Real.sq_sqrt hradPos
  have hradLower : 1 - e ≤ (1 - e) / x := by
    rw [le_div_iff₀ hxPos]
    exact mul_le_of_le_one_right (sub_nonneg.mpr he.2.le) hxLe
  change 1 - lrCertificateV point ^ 2 ≤ e
  rw [hvSq]
  linarith

lemma one_sub_v_bound
    {point : CertificatePoint} (hi : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) (hs : point.s ≤ 1 / 16) :
    1 - lrCertificateV point ≤ (51 / 100 : ℝ) * lrCertificateE point := by
  have hv := v_near_one hi hregion hs
  have hgap := one_sub_v_sq_le_e hi
  have hd : 0 ≤ 1 - lrCertificateV point :=
    sub_nonneg.mpr (lrCertificateV_mem_Ioo hi).2.le
  have hprod := mul_nonneg (sub_nonneg.mpr hv) hd
  have he := hi.2.1.1.le
  nlinarith

/-- The adverse radial weights are of order `e/2` and `e²/8`.
These rational bounds retain enough slack to avoid any numerical evaluator. -/
lemma weight_bounds
    {point : CertificatePoint} (hi : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point) (hs : point.s ≤ 1 / 16) :
    0 ≤ lrLowRatioAWeight point ∧
      lrLowRatioAWeight point ≤ 4 * lrCertificateE point ∧
      0 ≤ lrLowRatioBWeight point ∧
      lrLowRatioBWeight point ≤ (8 / 15 : ℝ) * lrCertificateE point ∧
      0 ≤ lrLowRatioKappa point ∧
      lrLowRatioKappa point ≤ (1 / 7 : ℝ) * lrCertificateE point ^ 2 := by
  let v := lrCertificateV point
  let e := lrCertificateE point
  let d := 1 - v
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hnear : (99 / 100 : ℝ) ≤ v := v_near_one hi hregion hs
  have hd0 : 0 ≤ d := sub_nonneg.mpr hv.2.le
  have he0 : 0 ≤ e := hi.2.1.1.le
  have hd : d ≤ (51 / 100 : ℝ) * e := one_sub_v_bound hi hregion hs
  have hdSq : d ^ 2 ≤ (2601 / 10000 : ℝ) * e ^ 2 := by nlinarith
  have hve := mul_nonneg (sub_nonneg.mpr hnear) he0
  have hvDen : (19701 / 10000 : ℝ) ≤ v * (1 + v) := by nlinarith
  rcases lrLowRatio_weight_identities hi with ⟨haEq, hbEq, hkEq⟩
  have ha0 : 0 ≤ lrLowRatioAWeight point := by
    rw [haEq]
    exact div_nonneg hd0 hv.1.le
  have haUpper : lrLowRatioAWeight point ≤ 4 * e := by
    rw [haEq, div_le_iff₀ hv.1]
    change d ≤ 4 * e * v
    nlinarith
  have hb0 : 0 ≤ lrLowRatioBWeight point := by
    rw [hbEq]
    exact div_nonneg (mul_nonneg (by norm_num) hd0) (by linarith [hv.1])
  have hbUpper : lrLowRatioBWeight point ≤ (8 / 15 : ℝ) * e := by
    rw [hbEq, div_le_iff₀ (by linarith [hv.1] : 0 < 1 + lrCertificateV point)]
    change 2 * d ≤ (8 / 15 : ℝ) * e * (1 + v)
    nlinarith
  have hk0 : 0 ≤ lrLowRatioKappa point := by
    rw [hkEq]
    exact div_nonneg (sq_nonneg _) (mul_nonneg hv.1.le (by linarith [hv.1]))
  have hkUpper : lrLowRatioKappa point ≤ (1 / 7 : ℝ) * e ^ 2 := by
    rw [hkEq, div_le_iff₀ (mul_pos hv.1 (by linarith [hv.1]))]
    change d ^ 2 ≤ (1 / 7 : ℝ) * e ^ 2 * (v * (1 + v))
    have hscale := mul_le_mul_of_nonneg_left hvDen (sq_nonneg e)
    nlinarith
  exact ⟨ha0, haUpper, hb0, hbUpper, hk0, hkUpper⟩

end CourtadeKumar.LRLowRatioAnalyticExtension
