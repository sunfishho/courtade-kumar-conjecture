import InformationTheory.CourtadeKumar.TopCapDerivative
import Mathlib.Analysis.Convex.Deriv

/-! Positivity and convexity facts behind the common-primitive reduction in
the corrected TOP cap argument. -/

open Set

namespace CourtadeKumar

noncomputable def topPsiSlopeGap (x : ℝ) : ℝ :=
  x / (1 - x ^ 2) - Real.artanh x

lemma hasDerivAt_topPsiSlopeGap {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt topPsiSlopeGap (2 * x ^ 2 / (1 - x ^ 2) ^ 2) x := by
  have hdenNe : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hid := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    convert hid.pow 2 using 1 <;> simp only [id_eq] <;> ring
  have hden := (hasDerivAt_const x 1).sub hsq
  have hfrac := hid.div hden hdenNe
  have hart := hasDerivAt_artanh hx
  unfold topPsiSlopeGap
  convert hfrac.sub hart using 1
  simp only [id_eq, Pi.sub_apply]
  field_simp [hdenNe]
  ring

lemma topPsiSlopeGap_nonneg {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    0 ≤ topPsiSlopeGap x := by
  have hdomain : ∀ y ∈ Icc (0 : ℝ) x, y ∈ Ioo (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hy.1], hy.2.trans_lt hx.2⟩
  have hmono : MonotoneOn topPsiSlopeGap (Icc (0 : ℝ) x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    · intro y hy
      exact (hasDerivAt_topPsiSlopeGap (hdomain y hy)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_topPsiSlopeGap
        (hdomain y (interior_subset hy))).hasDerivWithinAt
    · intro y hy
      positivity
  have h := hmono (show (0 : ℝ) ∈ Icc 0 x by simp [hx.1])
    (show x ∈ Icc 0 x by simp [hx.1]) hx.1
  simpa [topPsiSlopeGap] using h

noncomputable def topPsiDeriv2 (R : ℝ) : ℝ :=
  topPsiSlopeGap (Real.sqrt R) / (4 * Real.sqrt R ^ 3)

lemma hasDerivAt_topPsiDeriv {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt topPsiDeriv (topPsiDeriv2 R) R := by
  have hsqrt := Real.hasDerivAt_sqrt hR.1.ne'
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hsqrtMem : Real.sqrt R ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, hsqrtLt⟩
  have hart := (hasDerivAt_artanh hsqrtMem).comp R hsqrt
  have hden := hsqrt.const_mul 2
  have hquot := hart.div hden (mul_ne_zero (by norm_num) hsqrtPos.ne')
  have hsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  unfold topPsiDeriv topPsiDeriv2 topPsiSlopeGap
  convert hquot using 1
  simp only [Function.comp_apply]
  field_simp [hsqrtPos.ne', sub_ne_zero.mpr hR.2.ne]
  rw [hsq]
  ring

lemma topPsiDeriv2_nonneg {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topPsiDeriv2 R := by
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  unfold topPsiDeriv2
  exact div_nonneg
    (topPsiSlopeGap_nonneg ⟨hsqrtPos.le, hsqrtLt⟩)
    (by positivity)

theorem topPsiDeriv_monotoneOn :
    MonotoneOn topPsiDeriv (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo (0 : ℝ) 1)
  · intro R hR
    exact (hasDerivAt_topPsiDeriv hR).continuousAt.continuousWithinAt
  · intro R hR
    exact (hasDerivAt_topPsiDeriv
      (by simpa using hR)).hasDerivWithinAt
  · intro R hR
    exact topPsiDeriv2_nonneg (by simpa using hR)

lemma topPsi_convexOn_Icc {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    ConvexOn ℝ (Icc a b) (fun x : ℝ ↦ topPhi (Real.sqrt x)) := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Icc a b)
  · intro x hx
    exact (hasDerivAt_topPsi (hsub hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_topPsi (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(hasDerivAt_topPsi (hsub (interior_subset hx))).deriv,
      (hasDerivAt_topPsi (hsub (interior_subset hy))).deriv]
    exact topPsiDeriv_monotoneOn
      (hsub (interior_subset hx)) (hsub (interior_subset hy)) hxy

lemma topPsi_tangent_le {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) :
    (b - a) * topPsiDeriv a ≤
      topPhi (Real.sqrt b) - topPhi (Real.sqrt a) := by
  have hconv := topPsi_convexOn_Icc ha hb hab.le
  have hslope := hconv.le_slope_of_hasDerivAt
    (show a ∈ Icc a b by simp [hab.le])
    (show b ∈ Icc a b by simp [hab.le]) hab (hasDerivAt_topPsi ha)
  simp only [slope_def_field] at hslope
  have h := (le_div_iff₀ (sub_pos.mpr hab)).mp hslope
  simpa [mul_comm] using h

/-- The normalized energy term is increasing in the channel square.  This
is the positivity used when replacing `B` by `c B₀`. -/
theorem topChannelKDeriv_nonneg {R q : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topChannelKDeriv R q := by
  have ha : R * q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hq.1
    · have := mul_lt_mul_of_pos_right hR.2 hq.1
      nlinarith [hq.2]
  have hab : R * q < q := by
    simpa using mul_lt_mul_of_pos_right hR.2 hq.1
  have htangent := topPsi_tangent_le ha hq hab
  have hsqrtMul : Real.sqrt (R * q) = Real.sqrt R * Real.sqrt q := by
    rw [Real.sqrt_mul hR.1.le]
  have hsqrtRPos := Real.sqrt_pos.2 hR.1
  have hsqrtqPos := Real.sqrt_pos.2 hq.1
  have hA : q * topPsiDeriv (R * q) =
      Real.artanh (Real.sqrt R * Real.sqrt q) *
        (Real.sqrt q / (2 * Real.sqrt R)) := by
    unfold topPsiDeriv
    rw [hsqrtMul]
    field_simp [hsqrtRPos.ne', hsqrtqPos.ne']
    rw [Real.sq_sqrt hq.1.le]
  have hbase :
      q * (1 - R) * topPsiDeriv (R * q) ≤
        topPhi (Real.sqrt q) -
          topPhi (Real.sqrt R * Real.sqrt q) := by
    rw [← hsqrtMul]
    nlinarith [htangent]
  unfold topChannelKDeriv
  dsimp only
  rw [← hA]
  have hdenBase : 0 < (1 - R) * q :=
    mul_pos (sub_pos.mpr hR.2) hq.1
  have hden : 0 < ((1 - R) * q) ^ 2 := sq_pos_of_pos hdenBase
  apply div_nonneg
  · nlinarith [mul_nonneg hq.1.le
      (sub_nonneg.mpr hbase)]
  · exact hden.le

noncomputable def topCapB0 (c q : ℝ) : ℝ :=
  let R := topCapR c q
  (1 - R) ^ 2 *
    (topChannelWDeriv R - topChannelKDeriv R q)

lemma topCapB_eq_cB0_sub {c q : ℝ} :
    topCapB c q = c * topCapB0 c q -
      (1 - c) * (1 - topCapR c q) ^ 2 *
        topChannelKDeriv (topCapR c q) q := by
  unfold topCapB topCapB0
  dsimp only
  ring

/-- Removing the difficult channel difference can only increase the common
primitive. -/
theorem topCapB_le_cB0 {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapB c q ≤ c * topCapB0 c q := by
  rw [topCapB_eq_cB0_sub]
  have hk := topChannelKDeriv_nonneg (topCapR_mem_Ioo hc hq) hq
  have hcorr : 0 ≤ (1 - c) * (1 - topCapR c q) ^ 2 *
      topChannelKDeriv (topCapR c q) q := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hc.2.le) (sq_nonneg _)) hk
  linarith

end CourtadeKumar
