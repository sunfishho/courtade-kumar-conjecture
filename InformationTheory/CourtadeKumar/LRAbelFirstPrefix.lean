import InformationTheory.CourtadeKumar.LRAbelTailBound

/-! Positivity of the exceptional first Abel prefix. -/

open Set

namespace CourtadeKumar

noncomputable def lrLogTaylorGap (v : ℝ) : ℝ :=
  v - v ^ 2 / 2 + v ^ 3 / 3 - Real.log (1 + v)

theorem hasDerivAt_lrLogTaylorGap
    {v : ℝ} (hv : -1 < v) :
    HasDerivAt lrLogTaylorGap
      (1 - v + v ^ 2 - 1 / (1 + v)) v := by
  have hplus : 1 + v ≠ 0 := by linarith
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y)) (1 / (1 + v)) v := by
    simpa [one_div] using
      (((hasDerivAt_const v 1).add (hasDerivAt_id v)).log hplus)
  have h := (((hasDerivAt_id v).sub
    ((hasDerivAt_pow 2 v).div_const 2)).add
      ((hasDerivAt_pow 3 v).div_const 3)).sub hlog
  convert h using 1
  norm_num

theorem lrLogTaylorGap_nonneg
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLogTaylorGap v := by
  have hmono : MonotoneOn lrLogTaylorGap (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    · intro y hy
      exact (hasDerivAt_lrLogTaylorGap (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_lrLogTaylorGap (by linarith [hy.1])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hasDerivAt_lrLogTaylorGap (by linarith [hy.1])).deriv]
      have hden : 0 < 1 + y := by nlinarith [hy.1]
      have hid : 1 - y + y ^ 2 - 1 / (1 + y) = y ^ 3 / (1 + y) := by
        field_simp [hden.ne']
        ring
      rw [hid]
      exact div_nonneg (pow_nonneg hy.1.le _) hden.le
  have h := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hv hv.1
  simpa [lrLogTaylorGap] using h

theorem lr_log_one_add_cubic_upper
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    Real.log (1 + v) - v ^ 2 / 2 ≤
      v - v ^ 2 + v ^ 3 / 3 := by
  have hgap := lrLogTaylorGap_nonneg hv
  unfold lrLogTaylorGap at hgap
  linarith

theorem lrG_ge_two_log
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    2 * Real.log 2 ≤ lrG v := by
  have hanti : AntitoneOn lrG (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro y hy
      exact (hasDerivAt_lrG (lt_of_lt_of_le hv.1 hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_lrG (lt_trans hv.1 hy.1)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hypos : 0 < y := lt_trans hv.1 hy.1
      rw [(hasDerivAt_lrG hypos).deriv]
      have hlog : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) (sq_nonneg y)
  have h := hanti (show v ∈ Icc v (1 : ℝ) by exact ⟨le_rfl, hv.2⟩)
    (show (1 : ℝ) ∈ Icc v 1 by exact ⟨hv.2, le_rfl⟩) hv.2
  rwa [lrG_one] at h

/-- The first prefix displayed separately in the audited manuscript. -/
noncomputable def lrAbelFirstPrefix (v : ℝ) : ℝ :=
  lrG v - lrAbelCStar +
    (3 - v) / 2 * (v ^ 2 / 2 - Real.log (1 + v))

theorem lrAbelFirstPrefix_pos
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 < lrAbelFirstPrefix v := by
  have hvIcc : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
  have hG := lrG_ge_two_log hv
  have hlog := lr_log_one_add_cubic_upper hvIcc
  have hcubic := lr_one_third_cubic_bound hvIcc
  have hinner : -(1 / 3 : ℝ) ≤ v ^ 2 / 2 - Real.log (1 + v) := by
    linarith
  have hfactor0 : 0 ≤ (3 - v) / 2 := by nlinarith [hv.2]
  have hfactor1 : (3 - v) / 2 ≤ 3 / 2 := by nlinarith [hv.1]
  have hlower1 := mul_le_mul_of_nonneg_left hinner hfactor0
  have hlower2 := mul_le_mul_of_nonpos_right hfactor1 (by norm_num : (-1 / 3 : ℝ) ≤ 0)
  have hproduct : -(1 / 2 : ℝ) ≤
      (3 - v) / 2 * (v ^ 2 / 2 - Real.log (1 + v)) := by
    nlinarith
  have hmargin := lr_first_prefix_margin_pos
  unfold lrAbelFirstPrefix lrAbelCStar
  nlinarith

end CourtadeKumar
