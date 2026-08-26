import InformationTheory.CourtadeKumar.LRLowShapeLogTail

/-!
# Exact ratio subtraction for the `Q_n` tail

This module defines `Q_n`, verifies the finite reindexing and infinite-tail
recursion in the manuscript's subtraction formula, and proves the nonnegative
sign of its log-convexity sum using the explicit alpha-ratio ordering.
-/

open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowQ (xi : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    ((∑ k ∈ Finset.range (n - 1),
      xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) * lrLowAlpha (n - (k + 1))) +
      lrLowLogTail xi n)

lemma lrLowAlpha_one_lt_quarter : lrLowAlpha 1 < 1 / 4 := by
  have hlog := lr_log_two_millionth_bounds.1
  unfold lrLowAlpha lrLowCStar lrLowB lrLowA
  norm_num at hlog ⊢
  linarith

lemma lrLowQ_ratio_summand_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) {n k : ℕ} (hn : 2 ≤ n)
    (hk : k < n - 1) :
    0 ≤ xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
      (lrLowAlphaRatio n * lrLowAlpha (n - (k + 1)) -
        lrLowAlpha (n + 1 - (k + 1))) := by
  have hj : 1 ≤ n - (k + 1) := by omega
  have hjn : n - (k + 1) < n := by omega
  have horder := lrLowAlpha_ratio_order hj hjn
  change lrLowAlphaRatio (n - (k + 1)) ≤ lrLowAlphaRatio n at horder
  have hmul := mul_le_mul_of_nonneg_right horder
    (lrLowAlpha_pos (n - (k + 1))).le
  rw [lrLowAlphaRatio_mul_alpha] at hmul
  have hindex : n - (k + 1) + 1 = n + 1 - (k + 1) := by omega
  rw [hindex] at hmul
  exact mul_nonneg (div_nonneg (pow_nonneg hxi _) (by positivity))
    (sub_nonneg.mpr hmul)

lemma lrLowQ_ratio_sum_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ ∑ k ∈ Finset.range (n - 1),
      xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
        (lrLowAlphaRatio n * lrLowAlpha (n - (k + 1)) -
          lrLowAlpha (n + 1 - (k + 1))) := by
  apply Finset.sum_nonneg
  intro k hk
  exact lrLowQ_ratio_summand_nonneg hxi hn (Finset.mem_range.mp hk)

lemma lrLowQ_ratio_identity
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1)
    {n : ℕ} (hn : 2 ≤ n) :
    2 * (lrLowAlphaRatio n * lrLowQ xi n - lrLowQ xi (n + 1)) =
      (∑ k ∈ Finset.range (n - 1),
        xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
          (lrLowAlphaRatio n * lrLowAlpha (n - (k + 1)) -
            lrLowAlpha (n + 1 - (k + 1)))) +
      xi ^ n / (n : ℝ) * (lrLowAlphaRatio n - lrLowAlpha 1) -
      (1 - lrLowAlphaRatio n) * lrLowLogTail xi (n + 1) := by
  have htail := lrLowLogTail_recursion hxi0 hxi1 (show 1 ≤ n by omega)
  have hnSplit : n = (n - 1) + 1 := by omega
  have hsum :
      (∑ k ∈ Finset.range (n - 1),
        xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
          (lrLowAlphaRatio n * lrLowAlpha (n - (k + 1)) -
            lrLowAlpha (n + 1 - (k + 1)))) =
        lrLowAlphaRatio n *
          (∑ k ∈ Finset.range (n - 1),
            xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
              lrLowAlpha (n - (k + 1))) -
          (∑ k ∈ Finset.range (n - 1),
            xi ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
              lrLowAlpha (n + 1 - (k + 1))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold lrLowQ
  rw [show n + 1 - 1 = n by omega, hnSplit, Finset.sum_range_succ,
    show n - 1 + 1 = n by omega, show n + 1 - n = 1 by omega,
    htail, hsum]
  ring

end CourtadeKumar
