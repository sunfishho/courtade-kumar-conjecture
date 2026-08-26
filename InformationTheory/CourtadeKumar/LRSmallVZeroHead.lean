import InformationTheory.CourtadeKumar.LRSmallVPositiveCoefficients
import InformationTheory.CourtadeKumar.LRSmallVZeroFactor

/-!
# Quantitative head bound for the zeroth small-odds coefficient

This proves equation (109): the first coefficient in the remaining angular
series has a uniform positive margin.
-/

open Set

namespace CourtadeKumar

lemma lr_log_three_gt : (87 / 80 : ℝ) < Real.log 3 := by
  have hseries := lrAtanh5_le_two_artanh
    (show (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 by norm_num)
  have hpoly : (87 / 80 : ℝ) < lrAtanh5 (1 / 2) := by
    norm_num [lrAtanh5]
  have hart : 2 * Real.artanh (1 / 2 : ℝ) = Real.log 3 := by
    rw [Real.artanh_eq_half_log (show (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)]
    norm_num
    ring
  rw [hart] at hseries
  exact hpoly.trans_le hseries

noncomputable def lrSmallVZeroH (v : ℝ) : ℝ :=
  (1 + v) * (1 - Real.log v)

lemma hasDerivAt_lrSmallVZeroH
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt lrSmallVZeroH (-Real.log v - 1 / v) v := by
  have hlog := (hasDerivAt_id v).log hv.ne'
  have hleft := (hasDerivAt_const v 1).add (hasDerivAt_id v)
  have hright := (hasDerivAt_const v 1).sub hlog
  unfold lrSmallVZeroH
  convert hleft.mul hright using 1
  simp only [Pi.add_apply, Pi.sub_apply, id_eq]
  field_simp [hv.ne']
  ring

lemma lrSmallVZeroH_deriv_nonpos
    {v : ℝ} (hv : 0 < v) :
    deriv lrSmallVZeroH v ≤ 0 := by
  rw [(hasDerivAt_lrSmallVZeroH hv).deriv]
  have hlog := Real.one_sub_inv_le_log_of_pos hv
  rw [div_eq_mul_inv]
  linarith

theorem lrSmallVZeroH_ge_endpoint
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    lrSmallVZeroH (1 / 3) ≤ lrSmallVZeroH v := by
  have hanti : AntitoneOn lrSmallVZeroH (Icc v (1 / 3 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v (1 / 3 : ℝ))
    · intro x hx
      exact (hasDerivAt_lrSmallVZeroH (hv0.trans_le hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrSmallVZeroH (hv0.trans hx.1)).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact lrSmallVZeroH_deriv_nonpos (hv0.trans hx.1)
  exact hanti
    (show v ∈ Icc v (1 / 3 : ℝ) from ⟨le_rfl, hv⟩)
    (show (1 / 3 : ℝ) ∈ Icc v (1 / 3 : ℝ) from ⟨hv, le_rfl⟩) hv

theorem lrSmallV_zero_head_log_margin
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    (9 / 20 : ℝ) ≤
      (1 + v) * (1 - Real.log v) - 3 * lrLowCStar 1 := by
  have hH := lrSmallVZeroH_ge_endpoint hv0 hv
  have hlog3 := lr_log_three_gt.le
  have hlog2 := lr_log_two_millionth_bounds.2
  have hend : (9 / 20 : ℝ) ≤
      lrSmallVZeroH (1 / 3) - 3 * lrLowCStar 1 := by
    unfold lrSmallVZeroH lrLowCStar lrLowB lrLowA
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_one]
    norm_num
    linarith
  unfold lrSmallVZeroH at hH hend
  linarith

theorem lrSmallV_zero_gamma_one_lower
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    9 * v ^ 2 / (40 * (1 + v)) ≤
      v ^ 2 / 2 * (lrG v - lrLowCStar 1 / (1 + v)) -
        lrFlowBeta v * lrFlowM v * lrLowCStar 1 := by
  have hG : 1 - Real.log v ≤ lrG v := by
    have hden : 0 < 1 + v := by linarith
    have hlogLower := Real.one_sub_inv_le_log_of_pos hden
    have hcoef : 0 ≤ 1 + 1 / v := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlogLower hcoef
    unfold lrG
    have hone : (1 : ℝ) ≤ (1 + 1 / v) * Real.log (1 + v) := by
      calc
        (1 : ℝ) = (1 + 1 / v) * (1 - (1 + v)⁻¹) := by
          field_simp [hv0.ne', hden.ne']
          ring
        _ ≤ _ := hprod
    linarith
  have hbeta : lrFlowBeta v ≤ v := by
    unfold lrFlowBeta
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + v by linarith)
  have hc0 : 0 ≤ lrLowCStar 1 := by
    unfold lrLowCStar
    exact mul_nonneg (by norm_num) (lrLowB_pos 1).le
  have hneg : lrFlowBeta v * lrFlowM v * lrLowCStar 1 ≤
      v ^ 2 / (1 + v) * lrLowCStar 1 := by
    unfold lrFlowM
    have hscale : 0 ≤ v / (1 + v) * lrLowCStar 1 := by positivity
    have := mul_le_mul_of_nonneg_right hbeta hscale
    convert this using 1 <;> field_simp [show 1 + v ≠ 0 by linarith] <;> ring
  have hmargin := lrSmallV_zero_head_log_margin hv0 hv
  have hden : 0 < 1 + v := by linarith
  have hscale : 0 ≤ v ^ 2 / (2 * (1 + v)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmargin hscale
  have hGscaled := mul_le_mul_of_nonneg_left hG (sq_nonneg v)
  calc
    9 * v ^ 2 / (40 * (1 + v)) =
        v ^ 2 / (2 * (1 + v)) * (9 / 20) := by field_simp [hden.ne']; ring
    _ ≤ v ^ 2 / (2 * (1 + v)) *
        ((1 + v) * (1 - Real.log v) - 3 * lrLowCStar 1) := hscaled
    _ ≤ v ^ 2 / 2 * (lrG v - lrLowCStar 1 / (1 + v)) -
        v ^ 2 / (1 + v) * lrLowCStar 1 := by
      field_simp [hden.ne'] at hGscaled ⊢
      nlinarith
    _ ≤ v ^ 2 / 2 * (lrG v - lrLowCStar 1 / (1 + v)) -
        lrFlowBeta v * lrFlowM v * lrLowCStar 1 := by linarith

end CourtadeKumar
