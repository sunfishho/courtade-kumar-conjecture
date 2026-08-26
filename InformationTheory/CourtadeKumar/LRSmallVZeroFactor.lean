import InformationTheory.CourtadeKumar.LRSmallVDirectClosure
import InformationTheory.CourtadeKumar.LRLowShapeVZeroBridge

/-!
# Positivity of the first zeroth-coefficient factor on `v ≤ 1/3`

This proves the analytic sign of `f₁` uniformly for the full angular
interval.  It uses only the elementary logarithm tangent bound and the
kernel theorem `exp(1) < 3`.
-/

open Set

namespace CourtadeKumar

lemma lrSmallV_log_lt_neg_one
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    Real.log v < -1 := by
  rw [Real.log_lt_iff_lt_exp hv0]
  have he : Real.exp 1 < (3 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hinv : (1 / 3 : ℝ) < 1 / Real.exp 1 :=
    one_div_lt_one_div_of_lt (Real.exp_pos 1) he
  have hthird : v < 1 / Real.exp 1 := hv.trans_lt hinv
  simpa [Real.exp_neg] using hthird

lemma lrG_gt_two_smallV
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    2 < lrG v := by
  have hden : 0 < 1 + v := by linarith
  have hlogLower := Real.one_sub_inv_le_log_of_pos hden
  have hcoef : 0 ≤ 1 + 1 / v := by positivity
  have hprod := mul_le_mul_of_nonneg_left hlogLower hcoef
  have hprodOne : (1 : ℝ) ≤
      (1 + 1 / v) * Real.log (1 + v) := by
    calc
      (1 : ℝ) = (1 + 1 / v) * (1 - (1 + v)⁻¹) := by
        field_simp [hv0.ne', hden.ne']
        ring
      _ ≤ _ := hprod
  have hlogV := lrSmallV_log_lt_neg_one hv0 hv
  unfold lrG
  linarith

theorem lrLowVZeroF1_pos_smallV
    {v x : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < lrLowVZeroF1 v x := by
  have hG := lrG_gt_two_smallV hv0 hv
  have hvOne : v ≤ 1 := hv.trans (by norm_num)
  have hcPos : 0 ≤ lrLowCStar 1 := by
    unfold lrLowCStar
    exact mul_nonneg (by norm_num) (lrLowB_pos 1).le
  have hcLt : lrLowCStar 1 < 1 := by
    have ha := lrLowAlpha_pos 1
    norm_num [lrLowAlpha] at ha
    exact ha
  have hcDiv : lrLowCStar 1 / (1 + v) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hT := lrLowT_le_two
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv0.le, hvOne⟩) hx 1
  have hA : lrLowA 1 = (1 / 2 : ℝ) := by norm_num [lrLowA]
  unfold lrLowVZeroF1
  rw [hA]
  nlinarith

end CourtadeKumar
