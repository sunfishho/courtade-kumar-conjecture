import InformationTheory.CourtadeKumar.LRLowShapeConcreteTail

/-!
# Rational minorants for the finite low-shape `V` heads

This introduces the exact finite expressions whose Bernstein numerators are
certified in the supplied proof, together with the rational `c_n^*` bounds and
the manifest nonnegativity of the retained `E_n` heads for `2 ≤ n ≤ 7`.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowCStarLower (n : ℕ) : ℝ :=
  4 * ((693147 : ℝ) / 1000000 -
    ∑ k ∈ Finset.range n, lrLowA (k + 1))

noncomputable def lrLowCStarUpper (n : ℕ) : ℝ :=
  4 * lrLowBnUpper n

noncomputable def lrLowEHead (xi : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * lrLowL12 xi -
    (1 / 2 : ℝ) * ∑ k ∈ Finset.range (n - 1),
      ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) * xi ^ (k + 1)

noncomputable def lrLowVConstantUpper (v x : ℝ) : ℝ :=
  lrLowL12Upper (v ^ 2 * x) / (1 + v) +
    lrAtanh5Upper (v / (2 + v)) * lrFlowM v * x

noncomputable def lrLowVComparisonMinorant (v x : ℝ) (n : ℕ) : ℝ :=
  lrLowGShapeLower v x * lrLowEHead (v ^ 2 * x) n -
    (n : ℝ) * lrLowVConstantUpper v x * lrLowCStarUpper n +
    lrLowDelta v x / 2 *
      ∑ k ∈ Finset.range (n - 1),
        ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (v ^ 2 * x) ^ (k + 1) * lrLowCStarLower (n - (k + 1))

lemma lrLowCStarLower_le (n : ℕ) :
    lrLowCStarLower n ≤ lrLowCStar n := by
  have hlog := lr_log_two_millionth_bounds.1.le
  unfold lrLowCStarLower lrLowCStar lrLowB
  linarith

lemma lrLowCStar_le_upper (n : ℕ) :
    lrLowCStar n ≤ lrLowCStarUpper n := by
  unfold lrLowCStarUpper lrLowCStar
  exact mul_le_mul_of_nonneg_left (lrLowBn_le_upper n) (by norm_num)

lemma lrLowCStarUpper_nonneg (n : ℕ) : 0 ≤ lrLowCStarUpper n := by
  unfold lrLowCStarUpper
  exact mul_nonneg (by norm_num) (lrLowBnUpper_nonneg n)

lemma lrLowCStarLower_nonneg_head
    {n : ℕ} (hn : n ≤ 7) : 0 ≤ lrLowCStarLower n := by
  interval_cases n <;>
    norm_num [lrLowCStarLower, lrLowA, Finset.sum_range_succ]

lemma lrLowEHead_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) {n : ℕ} (hn2 : 2 ≤ n) (hn7 : n ≤ 7) :
    0 ≤ lrLowEHead xi n := by
  interval_cases n <;>
    norm_num [lrLowEHead, lrLowL12, Finset.sum_range_succ]
  all_goals
    nlinarith [pow_nonneg hxi 2, pow_nonneg hxi 3, pow_nonneg hxi 4,
      pow_nonneg hxi 5, pow_nonneg hxi 6, pow_nonneg hxi 7,
      pow_nonneg hxi 8, pow_nonneg hxi 9, pow_nonneg hxi 10,
      pow_nonneg hxi 11, pow_nonneg hxi 12]

end CourtadeKumar
