import InformationTheory.CourtadeKumar.LRSmallVEndpointClosure
import InformationTheory.CourtadeKumar.LRLowShapeTailClosedForms

/-!
# Tail contraction on the small-odds chart

Because `ξ = v²x ≤ 1/9`, both exact tails contract by the alpha ratio
already from index two.  This strengthens the general low-shape propagation,
whose larger rectangle only begins at index seven.
-/

namespace CourtadeKumar

lemma lrLowLogTail_succ_smallXi_bound
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 9) (n : ℕ) :
    lrLowLogTail ξ (n + 1) ≤ ξ ^ n / ((n : ℝ) + 1) * (1 / 8) := by
  have hξ1 : ξ < 1 := by norm_num at hξ ⊢; linarith
  have htail := lrLowLogTail_le_geometric hξ0 hξ1
    (show 1 ≤ n + 1 by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : (0 : ℝ) < 1 - ξ := by linarith
  have hfrac : ξ / (1 - ξ) ≤ 1 / 8 := by
    rw [div_le_iff₀ hone]
    norm_num at hξ ⊢
    linarith
  calc
    lrLowLogTail ξ (n + 1)
        ≤ ξ ^ (n + 1) / (((n + 1 : ℕ) : ℝ) * (1 - ξ)) := htail
    _ = ξ ^ n / ((n : ℝ) + 1) * (ξ / (1 - ξ)) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
    _ ≤ ξ ^ n / ((n : ℝ) + 1) * (1 / 8) :=
      mul_le_mul_of_nonneg_left hfrac
        (div_nonneg (pow_nonneg hξ0 _) hn1.le)

lemma lrLowQ_tail_penalty_smallXi
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 9)
    {n : ℕ} (hn : 1 ≤ n) :
    (1 - lrLowAlphaRatio n) * lrLowLogTail ξ (n + 1) ≤
      ξ ^ n / ((n : ℝ) + 1) * (1 / (8 * ((n : ℝ) + 1))) := by
  have htail0 := lrLowLogTail_nonneg hξ0 (show 1 ≤ n + 1 by omega)
  have hmul := mul_le_mul (lrLowAlphaRatio_one_sub_le hn)
    (lrLowLogTail_succ_smallXi_bound hξ0 hξ n)
    htail0 (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))
  calc
    (1 - lrLowAlphaRatio n) * lrLowLogTail ξ (n + 1) ≤
        (1 / ((n : ℝ) + 1)) *
          (ξ ^ n / ((n : ℝ) + 1) * (1 / 8)) := hmul
    _ = ξ ^ n / ((n : ℝ) + 1) *
        (1 / (8 * ((n : ℝ) + 1))) := by field_simp

lemma lrLowQ_smallXi_bracket_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ (3 * (n : ℝ) - 1) / (4 * n) -
      1 / (8 * ((n : ℝ) + 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  field_simp
  nlinarith

theorem lrLowQ_succ_le_alphaRatio_smallXi
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 9)
    {n : ℕ} (hn : 2 ≤ n) :
    lrLowQ ξ (n + 1) ≤ lrLowAlphaRatio n * lrLowQ ξ n := by
  have hξ1 : ξ < 1 := by norm_num at hξ ⊢; linarith
  have hid := lrLowQ_ratio_identity hξ0 hξ1 hn
  have hsum := lrLowQ_ratio_sum_nonneg hξ0 hn
  have hmain := lrLowQ_main_term_lower hξ0 (show 1 ≤ n by omega)
  have hpenalty := lrLowQ_tail_penalty_smallXi hξ0 hξ
    (show 1 ≤ n by omega)
  have hbracket := lrLowQ_smallXi_bracket_nonneg hn
  have hpow : 0 ≤ ξ ^ n / ((n : ℝ) + 1) := by positivity
  have hscaled :
      ξ ^ n / ((n : ℝ) + 1) * (1 / (8 * ((n : ℝ) + 1))) ≤
        ξ ^ n / ((n : ℝ) + 1) *
          ((3 * (n : ℝ) - 1) / (4 * n)) :=
    mul_le_mul_of_nonneg_left (sub_nonneg.mp hbracket) hpow
  have hdiff :
      0 ≤ 2 * (lrLowAlphaRatio n * lrLowQ ξ n - lrLowQ ξ (n + 1)) := by
    rw [hid]
    nlinarith
  nlinarith

theorem lrLowRTail_succ_le_alphaRatio_smallXi
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 9)
    {n : ℕ} (hn : 2 ≤ n) :
    lrLowRTail ξ (n + 1) ≤ lrLowAlphaRatio n * lrLowRTail ξ n := by
  have hξ1 : ξ < 1 := by norm_num at hξ ⊢; linarith
  have hcontract := lrLowRTail_succ_le_mul hξ0 hξ1 n
  have hratio := lrLowAlpha_ratio_ge (n := n) (by omega)
  have hnRatio : (1 / 9 : ℝ) ≤ (n : ℝ) / (n + 1) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hξRatio : ξ ≤ lrLowAlphaRatio n := by
    unfold lrLowAlphaRatio
    exact hξ.trans (hnRatio.trans hratio)
  exact hcontract.trans (mul_le_mul_of_nonneg_right hξRatio
    (lrLowRTail_nonneg hξ0 n))

theorem lrLow_tail_propagation_from_two
    {L F Q R : ℕ → ℝ} {Vstar C delta G : ℝ}
    (hF : ∀ n, 2 ≤ n →
      F n = C * lrLowAlpha n - delta * Q n - G * R n)
    (hL : ∀ n, 2 ≤ n → L n = F n + Vstar)
    (hQ : ∀ n, 2 ≤ n → Q (n + 1) ≤ lrLowAlphaRatio n * Q n)
    (hR : ∀ n, 2 ≤ n → R (n + 1) ≤ lrLowAlphaRatio n * R n)
    (hdelta : 0 ≤ delta) (hG : 0 ≤ G) (hVstar : 0 ≤ Vstar)
    (hL2 : 0 ≤ L 2) :
    ∀ n, 2 ≤ n → 0 ≤ L n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hL2
  | succ n hn ih =>
      exact lrLow_tail_step (by omega)
        (hF n hn) (hF (n + 1) (by omega))
        (hL n hn) (hL (n + 1) (by omega))
        (hQ n hn) (hR n hn) hdelta hG hVstar ih

end CourtadeKumar
