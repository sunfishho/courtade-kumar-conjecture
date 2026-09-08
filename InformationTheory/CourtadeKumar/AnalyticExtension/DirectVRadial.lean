import InformationTheory.CourtadeKumar.AnalyticExtension.RadialBounds

/-! Radial bounds for the exact direct-V argument through `s = 1/10`. -/
open Set
namespace CourtadeKumar.LRLowRatioDirectV

lemma v_near_one
    {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hk : LRDeterminantLowRatioRegion p) (hs : p.s ≤ 1 / 10) :
    (99 / 100 : ℝ) ≤ lrCertificateV p := by
  have hd := lrLowRatio_one_sub_v_le_e hi
  have he := lrLowRatioE_le_s_sq hi hk
  have hs0 := hi.1.1.le
  have hsSq : p.s ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by nlinarith
  nlinarith

lemma radial_gap
    {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hk : LRDeterminantLowRatioRegion p) (hs : p.s ≤ 1 / 10) :
    1 - lrCertificateV p ≤ (51 / 100 : ℝ) * lrCertificateE p := by
  have hv := v_near_one hi hk hs
  have hgap := LRLowRatioAnalyticExtension.one_sub_v_sq_le_e hi
  have hd : 0 ≤ 1 - lrCertificateV p :=
    sub_nonneg.mpr (lrCertificateV_mem_Ioo hi).2.le
  have hprod := mul_nonneg (sub_nonneg.mpr hv) hd
  have he := hi.2.1.1.le
  nlinarith

lemma kappa_bounds
    {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hk : LRDeterminantLowRatioRegion p) (hs : p.s ≤ 1 / 10) :
    0 ≤ lrLowRatioKappa p ∧
      lrLowRatioKappa p ≤ (1 / 7 : ℝ) * lrCertificateE p ^ 2 := by
  let v := lrCertificateV p
  let e := lrCertificateE p
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hn : (99 / 100 : ℝ) ≤ v := v_near_one hi hk hs
  have hd : 1 - v ≤ (51 / 100 : ℝ) * e := radial_gap hi hk hs
  have hd0 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have he0 : 0 ≤ e := hi.2.1.1.le
  have hsq : (1 - v) ^ 2 ≤ (2601 / 10000 : ℝ) * e ^ 2 := by nlinarith
  have hden : (19701 / 10000 : ℝ) ≤ v * (1 + v) := by nlinarith
  rw [(lrLowRatio_weight_identities hi).2.2]
  constructor
  · exact div_nonneg (sq_nonneg _) (mul_nonneg hv.1.le (by linarith [hv.1]))
  · rw [div_le_iff₀ (mul_pos hv.1 (by linarith [hv.1]))]
    have hscale := mul_le_mul_of_nonneg_left hden (sq_nonneg e)
    change (1 - v) ^ 2 ≤ (1 / 7 : ℝ) * e ^ 2 * (v * (1 + v))
    nlinarith

lemma g0Prime_upper {v : ℝ} (hv : v ∈ Icc (99 / 100 : ℝ) 1) :
    lrCertificateG0Prime v ≤ (3 / 5 : ℝ) * (1 - v) := by
  have hv0 : 0 < v := by linarith [hv.1]
  have hp : 0 < 1 + v := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hp)
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hlog
  have hquot : 2 / (1 + v) - 1 = (1 - v) / (1 + v) := by
    field_simp [hp.ne']
    ring
  rw [hquot] at hlog
  have hvsq : (9801 / 10000 : ℝ) ≤ v ^ 2 := by nlinarith [hv.1]
  have hcubic := mul_nonneg (sub_nonneg.mpr hv.1) (sq_nonneg v)
  have hden : (5 / 3 : ℝ) ≤ v ^ 2 * (1 + v) := by nlinarith
  have hd := mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hden)
  have hbound : (1 - v) / (1 + v) ≤ (3 / 5 : ℝ) * (1 - v) * v ^ 2 := by
    rw [div_le_iff₀ hp]
    nlinarith
  unfold lrCertificateG0Prime
  rw [div_le_iff₀ (sq_pos_of_pos hv0)]
  exact hlog.trans hbound

/-- A derivative bound retains the quadratic cancellation in g0 near one. -/
lemma g0_lower {v : ℝ} (hv : v ∈ Icc (99 / 100 : ℝ) 1) :
    -(3 / 10 : ℝ) * (1 - v) ^ 2 ≤ lrCertificateG0 v := by
  let f : ℝ → ℝ := fun w => lrCertificateG0 w + (3 / 10 : ℝ) * (1 - w) ^ 2
  have hderiv : ∀ w : ℝ, 0 < w → HasDerivAt f
      (lrCertificateG0Prime w - (3 / 5 : ℝ) * (1 - w)) w := by
    intro w hw
    have h := (hasDerivAt_lrCertificateG0 hw).add
      ((((hasDerivAt_const w 1).sub (hasDerivAt_id w)).pow 2).const_mul (3 / 10 : ℝ))
    convert h using 1 <;> dsimp [f] <;> ring
  have hanti : AntitoneOn f (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro w hw
      exact (hderiv w (by linarith [hw.1, hv.1])).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact (hderiv w (by linarith [hw.1, hv.1])).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hderiv w (by linarith [hw.1, hv.1])).deriv]
      exact sub_nonpos.mpr (g0Prime_upper ⟨by linarith [hv.1, hw.1], hw.2.le⟩)
  have h := hanti ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ hv.2
  have hone : f 1 = 0 := by norm_num [f, lrCertificateG0]
  rw [hone] at h
  dsimp [f] at h
  linarith

end CourtadeKumar.LRLowRatioDirectV
