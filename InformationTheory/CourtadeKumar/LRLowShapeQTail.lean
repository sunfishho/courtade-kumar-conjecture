import InformationTheory.CourtadeKumar.LRLowShapeQIdentity

/-!
# Contraction of the `Q_n` tail

The rational `log 2` bound, the geometric logarithmic-tail estimate, and the
alpha-ratio inequalities are combined exactly as in the supplied proof to
obtain `Q_(n+1) ≤ r_n Q_n` for every `n ≥ 7`.
-/

namespace CourtadeKumar

lemma lrLowAlphaRatio_one_sub_le
    {n : ℕ} (hn : 1 ≤ n) :
    1 - lrLowAlphaRatio n ≤ 1 / ((n : ℝ) + 1) := by
  have hratio := lrLowAlpha_ratio_ge (n := n) hn
  unfold lrLowAlphaRatio
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hn1] at hratio
  field_simp
  nlinarith

lemma lrLowLogTail_succ_rectangle_bound
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi : xi ≤ 17 / 20)
    (n : ℕ) :
    lrLowLogTail xi (n + 1) ≤
      xi ^ n / ((n : ℝ) + 1) * (17 / 3) := by
  have hxi1 : xi < 1 := by norm_num at hxi ⊢; linarith
  have htail := lrLowLogTail_le_geometric hxi0 hxi1
    (show 1 ≤ n + 1 by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : (0 : ℝ) < 1 - xi := by linarith
  have hfrac : xi / (1 - xi) ≤ 17 / 3 := by
    rw [div_le_iff₀ hone]
    norm_num at hxi ⊢
    nlinarith
  calc
    lrLowLogTail xi (n + 1)
        ≤ xi ^ (n + 1) / (((n + 1 : ℕ) : ℝ) * (1 - xi)) := htail
    _ = xi ^ n / ((n : ℝ) + 1) * (xi / (1 - xi)) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
    _ ≤ xi ^ n / ((n : ℝ) + 1) * (17 / 3) := by
      exact mul_le_mul_of_nonneg_left hfrac (div_nonneg (pow_nonneg hxi0 _) hn1.le)

lemma lrLowQ_main_term_lower
    {xi : ℝ} (hxi : 0 ≤ xi) {n : ℕ} (hn : 1 ≤ n) :
    xi ^ n / (n : ℝ) * (lrLowAlphaRatio n - lrLowAlpha 1) ≥
      xi ^ n / ((n : ℝ) + 1) * ((3 * (n : ℝ) - 1) / (4 * n)) := by
  have hratio := lrLowAlpha_ratio_ge (n := n) hn
  have hAlphaOne := lrLowAlpha_one_lt_quarter.le
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfactor : 0 ≤ xi ^ n / (n : ℝ) := div_nonneg (pow_nonneg hxi _) hnR.le
  have hinside :
      ((n : ℝ) / (n + 1) - 1 / 4) ≤
        lrLowAlphaRatio n - lrLowAlpha 1 := by
    unfold lrLowAlphaRatio
    linarith
  calc
    xi ^ n / ((n : ℝ) + 1) * ((3 * (n : ℝ) - 1) / (4 * n)) =
        xi ^ n / (n : ℝ) * ((n : ℝ) / (n + 1) - 1 / 4) := by
          field_simp
          ring
    _ ≤ xi ^ n / (n : ℝ) * (lrLowAlphaRatio n - lrLowAlpha 1) :=
      mul_le_mul_of_nonneg_left hinside hfactor

lemma lrLowQ_tail_penalty_upper
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi : xi ≤ 17 / 20)
    {n : ℕ} (hn : 1 ≤ n) :
    (1 - lrLowAlphaRatio n) * lrLowLogTail xi (n + 1) ≤
      xi ^ n / ((n : ℝ) + 1) * (17 / (3 * ((n : ℝ) + 1))) := by
  have hOneNonneg : 0 ≤ 1 - lrLowAlphaRatio n :=
    sub_nonneg.mpr (lrLowAlphaRatio_le_one hn)
  have hTailNonneg := lrLowLogTail_nonneg hxi0 (show 1 ≤ n + 1 by omega)
  have hmul := mul_le_mul (lrLowAlphaRatio_one_sub_le hn)
    (lrLowLogTail_succ_rectangle_bound hxi0 hxi n)
    hTailNonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))
  calc
    (1 - lrLowAlphaRatio n) * lrLowLogTail xi (n + 1) ≤
        (1 / ((n : ℝ) + 1)) *
          (xi ^ n / ((n : ℝ) + 1) * (17 / 3)) := hmul
    _ = xi ^ n / ((n : ℝ) + 1) * (17 / (3 * ((n : ℝ) + 1))) := by
      field_simp

lemma lrLowQ_bracket_nonneg {n : ℕ} (hn : 7 ≤ n) :
    0 ≤ (3 * (n : ℝ) - 1) / (4 * n) - 17 / (3 * ((n : ℝ) + 1)) := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  field_simp
  nlinarith

theorem lrLowQ_succ_le_alphaRatio
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi : xi ≤ 17 / 20)
    {n : ℕ} (hn : 7 ≤ n) :
    lrLowQ xi (n + 1) ≤ lrLowAlphaRatio n * lrLowQ xi n := by
  have hxi1 : xi < 1 := by norm_num at hxi ⊢; linarith
  have hid := lrLowQ_ratio_identity hxi0 hxi1 (show 2 ≤ n by omega)
  have hsum := lrLowQ_ratio_sum_nonneg hxi0 (show 2 ≤ n by omega)
  have hmain := lrLowQ_main_term_lower hxi0 (show 1 ≤ n by omega)
  have hpenalty := lrLowQ_tail_penalty_upper hxi0 hxi (show 1 ≤ n by omega)
  have hbracket := lrLowQ_bracket_nonneg hn
  have hpow : 0 ≤ xi ^ n / ((n : ℝ) + 1) := by positivity
  have hscaled :
      xi ^ n / ((n : ℝ) + 1) * (17 / (3 * ((n : ℝ) + 1))) ≤
        xi ^ n / ((n : ℝ) + 1) * ((3 * (n : ℝ) - 1) / (4 * n)) :=
    mul_le_mul_of_nonneg_left (sub_nonneg.mp hbracket) hpow
  have hdiff :
      0 ≤ 2 * (lrLowAlphaRatio n * lrLowQ xi n - lrLowQ xi (n + 1)) := by
    rw [hid]
    nlinarith
  nlinarith

end CourtadeKumar
