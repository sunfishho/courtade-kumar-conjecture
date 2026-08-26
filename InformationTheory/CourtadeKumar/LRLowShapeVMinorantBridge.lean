import InformationTheory.CourtadeKumar.LRLowShapeVMinorants

/-!
# Analytic dominance of the finite-head minorants

For `2 ≤ n ≤ 7`, the actual comparison is shown to dominate the rational
minorant coefficient-by-coefficient.  Thus the forthcoming Bernstein tables
only need to certify the explicitly rational expressions.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

lemma lrLowVConstant_le_upper
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowVComparisonConstant v (t ^ 2) ≤ lrLowVConstantUpper v (t ^ 2) := by
  have hq0 : 0 < v ^ 2 * t ^ 2 := mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hq1 : v ^ 2 * t ^ 2 < 1 := by
    have hvt : v * t < 1 := calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  have hsqrt := lrLow_sqrt_sq_product hv.1.le ht.1.le
  have hLtail := lrL_sqrt_tail_twelve_upper hq0 hq1
  rw [hsqrt] at hLtail
  have hL : lrL (v * t) ≤ lrLowL12Upper (v ^ 2 * t ^ 2) := by
    unfold lrLowL12Upper lrLowL12
    linarith
  have hbeta := (lrAtanh5_beta_bounds
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)).2
  have hden : 0 ≤ (1 + v)⁻¹ := inv_nonneg.mpr (by linarith [hv.1])
  have hM : 0 ≤ lrFlowM v := by
    unfold lrFlowM
    exact div_nonneg hv.1.le (by linarith [hv.1])
  have hMx : 0 ≤ lrFlowM v * t ^ 2 := by
    exact mul_nonneg hM (sq_nonneg t)
  unfold lrLowVComparisonConstant lrLowVConstantUpper
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
  have hfirst := mul_le_mul_of_nonneg_right hL hden
  have hsecond := mul_le_mul_of_nonneg_right hbeta hMx
  simpa [div_eq_mul_inv, mul_assoc] using add_le_add hfirst hsecond

lemma lrLowVConstant_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowVComparisonConstant v (t ^ 2) := by
  have hvt0 : 0 ≤ v * t := mul_nonneg hv.1.le ht.1.le
  have hvt1 : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  unfold lrLowVComparisonConstant lrFlowM
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
  exact add_nonneg
    (div_nonneg (lrL_nonneg hvt0 hvt1) (by linarith [hv.1]))
    (mul_nonneg (mul_nonneg (Real.log_nonneg (by linarith [hv.1]))
      (div_nonneg hv.1.le (by linarith [hv.1]))) (sq_nonneg t))

lemma lrLowEHead_le_actual
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    {n : ℕ} :
    lrLowEHead (v ^ 2 * t ^ 2) n ≤
      (n : ℝ) * lrL (v * t) -
        (1 / 2 : ℝ) * ∑ k ∈ Finset.range (n - 1),
          ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
            (v ^ 2 * t ^ 2) ^ (k + 1) := by
  have hvt : 0 < v * t := mul_pos hv.1 ht.1
  have hvt1 : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hq : v ^ 2 * t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    constructor
    · positivity
    · nlinarith [mul_pos hvt (sub_pos.mpr hvt1)]
  have hL := lrL_sqrt_partial_sum_le hq 12
  rw [lrLow_sqrt_sq_product hv.1.le ht.1.le] at hL
  unfold lrLowEHead lrLowL12
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg n)) _

theorem lrLowVComparisonMinorant_le
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    {n : ℕ} (hn2 : 2 ≤ n) (hn7 : n ≤ 7)
    (hGlow : 0 ≤ lrLowGShapeLower v (t ^ 2)) :
    lrLowVComparisonMinorant v (t ^ 2) n ≤
      lrLowVComparison v (t ^ 2) (lrGShape t v) n := by
  have hg := lrLowGShapeLower_le hv ht
  have hG0 : 0 ≤ lrGShape t v := hGlow.trans hg
  have hE0 := lrLowEHead_nonneg (mul_nonneg (sq_nonneg v) (sq_nonneg t)) hn2 hn7
  have hE := lrLowEHead_le_actual hv ht (n := n)
  have hGE := mul_le_mul hg hE hE0 hG0
  have hC := lrLowVConstant_le_upper hv ht
  have hC0 := lrLowVConstant_nonneg hv ht
  have hCU0 : 0 ≤ lrLowVConstantUpper v (t ^ 2) := hC0.trans hC
  have hc := lrLowCStar_le_upper n
  have hc0 : 0 ≤ lrLowCStar n := by
    unfold lrLowCStar
    exact mul_nonneg (by norm_num) (lrLowB_pos n).le
  have hcU0 := lrLowCStarUpper_nonneg n
  have hCprod :
      (n : ℝ) * lrLowVComparisonConstant v (t ^ 2) * lrLowCStar n ≤
        (n : ℝ) * lrLowVConstantUpper v (t ^ 2) * lrLowCStarUpper n := by
    have hp := mul_le_mul hC hc hc0 hCU0
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n)
  have hdelta : 0 ≤ lrLowDelta v (t ^ 2) / 2 := by
    unfold lrLowDelta
    have hvtsq : v * t ^ 2 ≤ 1 := by
      have htSq : t ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
      calc
        v * t ^ 2 ≤ 1 * t ^ 2 := mul_le_mul_of_nonneg_right hv.2.le (sq_nonneg t)
        _ ≤ 1 := by simpa using htSq
    exact div_nonneg (div_nonneg (sub_nonneg.mpr hvtsq) (by linarith [hv.1]))
      (by norm_num)
  have hsum :
      (∑ k ∈ Finset.range (n - 1),
        ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (v ^ 2 * t ^ 2) ^ (k + 1) * lrLowCStarLower (n - (k + 1))) ≤
      (∑ k ∈ Finset.range (n - 1),
        ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (v ^ 2 * t ^ 2) ^ (k + 1) * lrLowCStar (n - (k + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hweight : 0 ≤
        ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (v ^ 2 * t ^ 2) ^ (k + 1) := by positivity
    exact mul_le_mul_of_nonneg_left (lrLowCStarLower_le _) hweight
  have hconv := mul_le_mul_of_nonneg_left hsum hdelta
  unfold lrLowVComparisonMinorant lrLowVComparison
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
  nlinarith

end CourtadeKumar
