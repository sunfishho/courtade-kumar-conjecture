import InformationTheory.CourtadeKumar.LRLowShapeTailClosedForms

/-!
# Decomposition of the concrete low-shape comparison

This is the exact bridge from `lrLowVComparison` to the tail quantities used
by the propagation theorem.  In manuscript notation it proves
`ℒ_n - V_* = C_*α_n - δQ_n - G R_n`.
-/

open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowVStar (v x G : ℝ) : ℝ :=
  v ^ 2 * x / (2 * (1 - v ^ 2 * x)) * G -
    lrFlowA v (Real.sqrt x) * lrFlowM v * x

noncomputable def lrLowFComparison (v x G : ℝ) (n : ℕ) : ℝ :=
  lrLowVComparison v x G n - lrLowVStar v x G

lemma lrLowAlpha_cstar (n : ℕ) :
    (n : ℝ) * lrLowCStar n = 1 - lrLowAlpha n := by
  unfold lrLowAlpha lrLowCStar
  ring

lemma lrLowVConstant_balance (v x : ℝ) :
    lrLowVComparisonConstant v x =
      lrFlowA v (Real.sqrt x) * lrFlowM v * x +
        lrLowDelta v x * lrL (v * Real.sqrt x) := by
  unfold lrLowVComparisonConstant lrFlowA lrFlowM lrLowDelta
  by_cases hv : 1 + v = 0
  · rw [hv]
    norm_num
  · field_simp [hv]
    ring

lemma lrLow_weighted_cstar_sum
    {xi : ℝ} {n : ℕ} :
    (∑ k ∈ Finset.range (n - 1),
      ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
        xi ^ (k + 1) * lrLowCStar (n - (k + 1))) =
      (∑ k ∈ Finset.range (n - 1),
        xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
          (1 - lrLowAlpha (n - (k + 1)))) := by
  apply Finset.sum_congr rfl
  intro k hk
  have hklt := Finset.mem_range.mp hk
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hc := lrLowAlpha_cstar (n - (k + 1))
  field_simp [hpos.ne']
  calc
    ((n - (k + 1) : ℕ) : ℝ) * xi ^ (k + 1) *
          lrLowCStar (n - (k + 1)) =
        xi ^ (k + 1) *
          (((n - (k + 1) : ℕ) : ℝ) * lrLowCStar (n - (k + 1))) := by ring
    _ = xi ^ (k + 1) * (1 - lrLowAlpha (n - (k + 1))) := by rw [hc]

lemma lrLow_geometric_prefix_tail
    {xi : ℝ} (hxi : xi ≠ 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, xi ^ (k + 1)) +
        xi ^ (n + 1) / (1 - xi) = xi / (1 - xi) := by
  have hgeom := geom_sum_mul xi n
  have hprefix :
      (∑ k ∈ Finset.range n, xi ^ (k + 1)) =
        xi * (∑ k ∈ Finset.range n, xi ^ k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ']
  have hden : 1 - xi ≠ 0 := sub_ne_zero.mpr hxi.symm
  field_simp [hden]
  rw [hprefix]
  rw [pow_succ]
  linear_combination -xi * hgeom

lemma lrLow_weighted_plain_sum
    {xi : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n - 1),
      ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) * xi ^ (k + 1)) =
      (n : ℝ) *
          (∑ k ∈ Finset.range (n - 1),
            xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
        (∑ k ∈ Finset.range (n - 1), xi ^ (k + 1)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkRange := Finset.mem_range.mp hk
  have hklt : k + 1 ≤ n := by omega
  have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Nat.cast_sub hklt]
  field_simp [hden.ne']

lemma lrLow_G_bracket_eq_neg_R
    {xi : ℝ} (hxi0 : 0 < xi) (hxi1 : xi < 1)
    {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * lrL (Real.sqrt xi) -
        (1 / 2 : ℝ) *
          (∑ k ∈ Finset.range (n - 1),
            ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
              xi ^ (k + 1)) -
        xi / (2 * (1 - xi)) =
      -lrLowRTail xi n := by
  have hL := lrL_sqrt_eq_prefix_add_logTail hxi0 hxi1
    (show 1 ≤ n by omega)
  have hR := lrLowRTail_eq_logTail hxi0.le hxi1 n
  have htail := lrLowLogTail_recursion hxi0.le hxi1
    (show 1 ≤ n by omega)
  have hweighted := lrLow_weighted_plain_sum (xi := xi) hn
  have hgeom := lrLow_geometric_prefix_tail (show xi ≠ 1 by linarith) n
  have hnSplit : n = (n - 1) + 1 := by omega
  rw [hnSplit, Finset.sum_range_succ] at hgeom
  rw [hL, hR, htail, hweighted]
  have hpowN : xi ^ n = xi * xi ^ (n - 1) := by
    conv_lhs => rw [hnSplit, pow_succ]
    ring
  have hpowSucc : xi ^ (n + 1) = xi ^ 2 * xi ^ (n - 1) := by
    rw [pow_succ, hpowN]
    ring
  rw [hpowN, hpowSucc]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hden : 1 - xi ≠ 0 := by linarith
  field_simp [hn0, hden] at hgeom ⊢
  ring_nf at hgeom ⊢
  nlinarith [hgeom]

lemma lrLow_sqrt_vsq_mul
    {v x : ℝ} (hv : 0 ≤ v) :
    Real.sqrt (v ^ 2 * x) = v * Real.sqrt x := by
  rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq_eq_abs, abs_of_nonneg hv]

theorem lrLowFComparison_eq_C_alpha_sub_tails
    {v x G : ℝ} (hv : 0 < v) (hx : 0 < x)
    (hxi : v ^ 2 * x < 1) {n : ℕ} (hn : 2 ≤ n) :
    lrLowFComparison v x G n =
      lrLowVComparisonConstant v x * lrLowAlpha n -
        lrLowDelta v x * lrLowQ (v ^ 2 * x) n -
        G * lrLowRTail (v ^ 2 * x) n := by
  have hxi0 : 0 < v ^ 2 * x := mul_pos (sq_pos_of_pos hv) hx
  have hsqrt := lrLow_sqrt_vsq_mul (x := x) hv.le
  have hG := lrLow_G_bracket_eq_neg_R hxi0 hxi hn
  rw [hsqrt] at hG
  have hL := lrL_sqrt_eq_prefix_add_logTail hxi0 hxi
    (show 1 ≤ n by omega)
  rw [hsqrt] at hL
  have hC := lrLowVConstant_balance v x
  have hc := lrLowAlpha_cstar n
  have hcsum := lrLow_weighted_cstar_sum (xi := v ^ 2 * x) (n := n)
  unfold lrLowFComparison lrLowVComparison lrLowVStar lrLowQ
  rw [hcsum]
  have hplainAlpha :
      (∑ k ∈ Finset.range (n - 1),
        (v ^ 2 * x) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
          (1 - lrLowAlpha (n - (k + 1)))) =
        (∑ k ∈ Finset.range (n - 1),
          (v ^ 2 * x) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
        (∑ k ∈ Finset.range (n - 1),
          (v ^ 2 * x) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
            lrLowAlpha (n - (k + 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hplainAlpha]
  rw [show (n : ℝ) * lrLowVComparisonConstant v x * lrLowCStar n =
      lrLowVComparisonConstant v x * (1 - lrLowAlpha n) by
        rw [← hc]; ring]
  rw [hC]
  have hdeltaL :
      lrLowDelta v x * lrL (v * Real.sqrt x) =
        lrLowVComparisonConstant v x -
          lrFlowA v (Real.sqrt x) * lrFlowM v * x := by linarith [hC]
  rw [hL] at hdeltaL
  linear_combination G * hG + hdeltaL + hC

end CourtadeKumar
