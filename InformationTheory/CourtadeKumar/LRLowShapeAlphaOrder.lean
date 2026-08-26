import InformationTheory.CourtadeKumar.LRLowShapeAlphaRatio

/-!
# Ordering the low-shape alpha ratios

Rather than importing an abstract log-convex moment theorem, this module proves
the precise ratio comparison needed later.  A two-term rational lower envelope
for `b_n` gives an upper bound on each earlier ratio, while
`lrLowAlpha_ratio_ge` gives the matching lower bound on the later ratio.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowBLower (j : ℕ) : ℝ :=
  1 / (2 * (2 * (j : ℝ) + 1)) +
    1 / (4 * (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2))

lemma lrLowBLower_nonneg (j : ℕ) : 0 ≤ lrLowBLower j := by
  unfold lrLowBLower
  positivity

lemma lrLowBLower_diff_nonneg (j : ℕ) :
    0 ≤ lrLowBLower j - lrLowBLower (j + 1) := by
  unfold lrLowBLower
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  ring_nf
  nlinarith [sq_nonneg (j : ℝ)]

lemma lrLowBLower_diff_le_A (j : ℕ) :
    lrLowBLower j - lrLowBLower (j + 1) ≤ lrLowA (j + 1) := by
  unfold lrLowA lrLowBLower
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  ring_nf
  have hd : 0 < 1 + (j : ℝ) * 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hd
  field_simp
  ring_nf
  nlinarith

lemma lrLowBLower_le_simple (j : ℕ) :
    lrLowBLower j ≤ 1 / ((j : ℝ) + 1) := by
  unfold lrLowBLower
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  ring_nf
  nlinarith

lemma lrLowBLower_tendsto_zero :
    Filter.Tendsto lrLowBLower Filter.atTop (nhds 0) := by
  apply squeeze_zero (lrLowBLower_nonneg) (lrLowBLower_le_simple)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma lrLowBLower_diff_hasSum (j : ℕ) :
    HasSum (fun k : ℕ ↦
      lrLowBLower (k + j) - lrLowBLower (k + j + 1))
      (lrLowBLower j) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k ↦ lrLowBLower_diff_nonneg (k + j))]
  have hshift : Filter.Tendsto (fun n : ℕ ↦ lrLowBLower (n + j))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat j).2 lrLowBLower_tendsto_zero
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ lrLowBLower j)
      Filter.atTop (nhds (lrLowBLower j)) := tendsto_const_nhds
  have hlim := hconst.sub hshift
  have hsum (n : ℕ) :
      ∑ i ∈ Finset.range n,
          (lrLowBLower (i + j) - lrLowBLower (i + j + 1)) =
        lrLowBLower j - lrLowBLower (n + j) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      Finset.sum_range_sub' (fun i ↦ lrLowBLower (i + j)) n
  convert hlim using 1
  · funext n
    exact hsum n
  · simp

theorem lrLowBLower_le_B (j : ℕ) : lrLowBLower j ≤ lrLowB j := by
  have hl := lrLowBLower_diff_hasSum j
  have hb := lrLowB_hasSum j
  rw [← hl.tsum_eq, ← hb.tsum_eq]
  exact hl.summable.tsum_le_tsum
    (fun k ↦ lrLowBLower_diff_le_A (k + j)) hb.summable

lemma lrLowBLower_succ_ge_ratio_threshold (n : ℕ) :
    (4 * (n : ℝ) + 1) / (8 * (n + 1) * (2 * n + 1)) ≤
      lrLowBLower (n + 1) := by
  unfold lrLowBLower
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  field_simp
  ring_nf
  norm_num

lemma lrLowAlpha_ratio_le_next
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowAlpha (n + 1) / lrLowAlpha n ≤
      (n + 1 : ℝ) / (n + 2) := by
  rw [div_le_div_iff₀ (lrLowAlpha_pos n) (by positivity : (0 : ℝ) < n + 2)]
  have hb := (lrLowBLower_succ_ge_ratio_threshold n).trans
    (lrLowBLower_le_B (n + 1))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lrLowAlpha lrLowCStar
  rw [lrLowB_recursion n]
  unfold lrLowA
  norm_num only [Nat.cast_add, Nat.cast_one] at hb ⊢
  ring_nf at hb ⊢
  field_simp at hb ⊢
  ring_nf at hb ⊢
  nlinarith

theorem lrLowAlpha_ratio_order
    {j n : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    lrLowAlpha (j + 1) / lrLowAlpha j ≤
      lrLowAlpha (n + 1) / lrLowAlpha n := by
  calc
    lrLowAlpha (j + 1) / lrLowAlpha j
        ≤ (j + 1 : ℝ) / (j + 2) := lrLowAlpha_ratio_le_next hj
    _ ≤ (n : ℝ) / (n + 1) := by
      have hjR : (0 : ℝ) < j + 2 := by positivity
      have hnR : (0 : ℝ) < n + 1 := by positivity
      rw [div_le_div_iff₀ hjR hnR]
      exact_mod_cast (show (j + 1) * (n + 1) ≤ n * (j + 2) by
        nlinarith)
    _ ≤ lrLowAlpha (n + 1) / lrLowAlpha n :=
      lrLowAlpha_ratio_ge (by omega)

end CourtadeKumar
