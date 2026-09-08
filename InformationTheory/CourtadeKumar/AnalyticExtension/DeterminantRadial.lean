import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantElementary

/-! Uniform radial weights on 0 < s ≤ 1/10, 0 < k ≤ 4. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

lemma finite_weight_bounds {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    0 ≤ lrLowRatioBWeight p ∧ lrLowRatioBWeight p ≤ (2 / 3 : ℝ) * lrCertificateE p ∧
    0 ≤ lrLowRatioKappa p ∧ lrLowRatioKappa p ≤ lrCertificateE p ^ 2 / 4 := by
  let v := lrCertificateV p
  let e := lrCertificateE p
  let d := 1 - v
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hvLo : (3 / 4 : ℝ) ≤ v := LRAnalyticMidpoint.v_lower hi hs hk
  have he : 0 ≤ e := hi.2.1.1.le
  have hd : 0 ≤ d := sub_nonneg.mpr hv.2.le
  have hgeom : d * (1 + v) ≤ e := by
    dsimp [d, v, e]
    nlinarith [LRLowRatioAnalyticExtension.one_sub_v_sq_le_e hi]
  have hdU : d ≤ (4 / 7 : ℝ) * e := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hvLo)]
  have hsq : d ^ 2 ≤ (16 / 49 : ℝ) * e ^ 2 := by nlinarith
  have hden : (21 / 16 : ℝ) ≤ v * (1 + v) := by nlinarith [hvLo]
  rcases lrLowRatio_weight_identities hi with ⟨_ha, hb, hkap⟩
  rw [hb, hkap]
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · rw [div_le_iff₀ (by linarith [hv.1] : 0 < 1 + lrCertificateV p)]
    change 2 * d ≤ 2 / 3 * e * (1 + v)
    nlinarith [mul_nonneg he (sub_nonneg.mpr hvLo)]
  · rw [div_le_iff₀ (mul_pos hv.1 (by linarith : 0 < 1 + v))]
    change d ^ 2 ≤ e ^ 2 / 4 * (v * (1 + v))
    nlinarith [mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hden)]

lemma delta_upper {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrDeterminantDelta p ≤ (4 / 7 : ℝ) * lrCertificateE p := by
  let v := lrCertificateV p
  let x := lrCertificateX p
  let e := lrCertificateE p
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hvLo : (3 / 4 : ℝ) ≤ v := LRAnalyticMidpoint.v_lower hi hs hk
  have hx : 0 < x := by
    dsimp [x, lrCertificateX]
    nlinarith [mul_lt_mul_of_pos_right hi.2.2.2 hi.2.1.1, hi.2.1.2]
  have hvSq : v ^ 2 * x = 1 - e := by
    have h := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hi.2.1.2.le) hx.le)
    change v ^ 2 = (1 - e) / x at h
    exact (eq_div_iff hx.ne').mp h
  have hnum : 1 - v * x ≤ e := by
    have hv2 : v ^ 2 ≤ v := by nlinarith [hv.1, hv.2]
    nlinarith [mul_le_mul_of_nonneg_right hv2 hx.le]
  unfold lrDeterminantDelta
  rw [div_le_iff₀ (by linarith [hv.1] : 0 < 1 + v)]
  change 1 - v * x ≤ 4 / 7 * e * (1 + v)
  nlinarith [mul_nonneg hi.2.1.1.le (sub_nonneg.mpr hvLo)]

/-- The g0 loss is paid by the positive D-weighted channel change. -/
lemma radial_d_payment {p : CertificatePoint} {D : ℝ}
    (hi : LRHighShapeInterior p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4)
    (hD : 0 ≤ D) :
    0 ≤ D * lrCertificateG0 (lrCertificateV p) +
      lrLowRatioBWeight p * (lrCertificateE p / 4 *
        (D * (1 - p.s + 2 * (Real.log 2 - Real.log (1 + lrCertificateV p))))) := by
  let v := lrCertificateV p
  let d := 1 - v
  let e := lrCertificateE p
  let b := lrLowRatioBWeight p
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hvLo : (3 / 4 : ℝ) ≤ v := LRAnalyticMidpoint.v_lower hi hs hk
  have hb : b = 2 * d / (1 + v) := (lrLowRatio_weight_identities hi).2.1
  have hb0 : 0 ≤ b := (finite_weight_bounds hi hs hk).1
  have hg := g0_finite_lower ⟨hvLo, hv.2.le⟩
  have hgeom : d * (1 + v) ≤ e := by
    dsimp [d, v, e]
    nlinarith [LRLowRatioAnalyticExtension.one_sub_v_sq_le_e hi]
  have hgood : d ^ 2 / 2 ≤ b * e / 4 := by
    rw [hb]
    apply (le_of_mul_le_mul_right ?_ (by linarith [hv.1] : 0 < 1 + v))
    field_simp [show 1 + v ≠ 0 by linarith [hv.1]]
    nlinarith [mul_le_mul_of_nonneg_left hgeom (show 0 ≤ d from sub_nonneg.mpr hv.2.le)]
  have hbeta : 0 ≤ Real.log 2 - Real.log (1 + v) := sub_nonneg.mpr
    (Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2]))
  have hcoef : (9 / 10 : ℝ) ≤ 1 - p.s + 2 * (Real.log 2 - Real.log (1 + v)) := by
    linarith
  have h1 := mul_le_mul_of_nonneg_left hg hD
  have h2 := mul_le_mul_of_nonneg_left hcoef (mul_nonneg (mul_nonneg hb0 hi.2.1.1.le) hD)
  have h3 := mul_le_mul_of_nonneg_left hgood hD
  change 0 ≤ D * lrCertificateG0 v + b * (e / 4 *
    (D * (1 - p.s + 2 * (Real.log 2 - Real.log (1 + v)))))
  dsimp [d] at h3
  nlinarith [mul_nonneg hD (sq_nonneg (1 - v))]

end CourtadeKumar.LRAnalyticDeterminant
