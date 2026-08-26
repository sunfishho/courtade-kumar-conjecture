import InformationTheory.CourtadeKumar.LRLowShapeBUpper

/-!
# The key ratio bound for the low-shape Hausdorff moments

This proves the exact estimate `n / (n + 1) ≤ α_(n+1) / α_n` from the
supplied proof.  Positivity and the ratio estimate are reduced to the rational
upper envelope for `b_n`; no numerical decision procedure is used.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowAlpha (n : ℕ) : ℝ :=
  1 - (n : ℝ) * lrLowCStar n

lemma lrLowBUpper_lt_quarter_inv
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowBUpper n < 1 / (4 * (n : ℝ)) := by
  unfold lrLowBUpper
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  field_simp
  ring_nf
  rw [← sub_pos]
  ring_nf
  positivity

theorem lrLowAlpha_pos (n : ℕ) : 0 < lrLowAlpha n := by
  rcases n with _ | n
  · norm_num [lrLowAlpha]
  have hb := lrLowB_le_upper (n + 1)
  have hu := lrLowBUpper_lt_quarter_inv (n := n + 1) (by omega)
  unfold lrLowAlpha lrLowCStar
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := hb.trans_lt hu
  have hmul : lrLowB (n + 1) * (4 * ((n : ℝ) + 1)) < 1 :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((n : ℝ) + 1))).mp
      (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  nlinarith

lemma lrLowBUpper_succ_le_ratio_threshold (n : ℕ) :
    lrLowBUpper (n + 1) ≤
      (4 * (n : ℝ) ^ 2 + 3 * n + 1) /
        (4 * (n + 1) * (2 * n + 1) ^ 2) := by
  unfold lrLowBUpper
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  field_simp
  ring_nf
  rw [← sub_nonneg]
  ring_nf
  positivity

theorem lrLowAlpha_ratio_ge
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / (n + 1) ≤ lrLowAlpha (n + 1) / lrLowAlpha n := by
  have hAlpha := lrLowAlpha_pos n
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 1) hAlpha]
  have hb := (lrLowB_le_upper (n + 1)).trans
    (lrLowBUpper_succ_le_ratio_threshold n)
  have hrec := lrLowB_recursion n
  unfold lrLowAlpha lrLowCStar
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [hrec]
  unfold lrLowA
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring_nf
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  field_simp [hn1.ne', h2n1.ne'] at hb ⊢
  ring_nf at hb ⊢
  nlinarith

end CourtadeKumar
