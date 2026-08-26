import InformationTheory.CourtadeKumar.LRLowShapeTailPropagation

/-!
# The geometric `R_n` tail

This realizes the manuscript's `R_n` as a convergent nonnegative series and
proves `R_(n+1) ≤ ξ R_n ≤ r_n R_n` on the low-shape rectangle.
-/

namespace CourtadeKumar

noncomputable def lrLowRTail (xi : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) / (k + n + 1) * xi ^ (k + n + 1) / 2

lemma lrLowR_term_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) (n k : ℕ) :
    0 ≤ ((k + 1 : ℕ) : ℝ) / (k + n + 1) * xi ^ (k + n + 1) / 2 := by
  positivity

lemma summable_lrLowR
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1) (n : ℕ) :
    Summable (fun k : ℕ ↦
      ((k + 1 : ℕ) : ℝ) / (k + n + 1) * xi ^ (k + n + 1) / 2) := by
  let g : ℕ → ℝ := fun k ↦ (xi ^ (n + 1) / 2) * xi ^ k
  have hg : Summable g :=
    (summable_geometric_of_lt_one hxi0 hxi1).mul_left (xi ^ (n + 1) / 2)
  apply Summable.of_nonneg_of_le (fun k ↦ lrLowR_term_nonneg hxi0 n k) _ hg
  intro k
  have hden : (0 : ℝ) < k + n + 1 := by positivity
  have hfrac : ((k + 1 : ℕ) : ℝ) / (k + n + 1) ≤ 1 := by
    rw [div_le_one hden]
    exact_mod_cast (show k + 1 ≤ k + n + 1 by omega)
  have hpow : 0 ≤ xi ^ (k + n + 1) := pow_nonneg hxi0 _
  calc
    ((k + 1 : ℕ) : ℝ) / (k + n + 1) * xi ^ (k + n + 1) / 2
        ≤ 1 * xi ^ (k + n + 1) / 2 := by gcongr
    _ = g k := by
      dsimp [g]
      rw [show k + n + 1 = (n + 1) + k by omega, pow_add]
      ring

lemma lrLowRTail_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) (n : ℕ) : 0 ≤ lrLowRTail xi n := by
  unfold lrLowRTail
  exact tsum_nonneg (fun k ↦ lrLowR_term_nonneg hxi n k)

lemma lrLowRTail_succ_le_mul
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1) (n : ℕ) :
    lrLowRTail xi (n + 1) ≤ xi * lrLowRTail xi n := by
  unfold lrLowRTail
  rw [← tsum_mul_left]
  exact (summable_lrLowR hxi0 hxi1 (n + 1)).tsum_le_tsum (fun k ↦ by
    have hden : (0 : ℝ) < k + n + 1 := by positivity
    have hdenSucc : (0 : ℝ) < k + (n + 1) + 1 := by positivity
    have hfrac :
        ((k + 1 : ℕ) : ℝ) / (k + (n + 1) + 1) ≤
          ((k + 1 : ℕ) : ℝ) / (k + n + 1) := by
      exact div_le_div_of_nonneg_left (by positivity) hden
        (by exact_mod_cast (show k + n + 1 ≤ k + (n + 1) + 1 by omega))
    have hpow : 0 ≤ xi ^ (k + n + 1) := pow_nonneg hxi0 _
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [show k + (n + 1) + 1 = (k + n + 1) + 1 by omega, pow_succ]
    calc
      (((k : ℝ) + 1) / ((k : ℝ) + ((n : ℝ) + 1) + 1) *
            (xi ^ (k + n + 1) * xi)) / 2
          ≤ (((k : ℝ) + 1) / ((k : ℝ) + (n : ℝ) + 1) *
            (xi ^ (k + n + 1) * xi)) / 2 := by
              gcongr
              norm_num
      _ = xi * ((((k : ℝ) + 1) / ((k : ℝ) + (n : ℝ) + 1) *
            xi ^ (k + n + 1)) / 2) := by ring)
    ((summable_lrLowR hxi0 hxi1 n).mul_left xi)

lemma lrLowRTail_succ_le_alphaRatio
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi : xi ≤ 17 / 20)
    {n : ℕ} (hn : 7 ≤ n) :
    lrLowRTail xi (n + 1) ≤ lrLowAlphaRatio n * lrLowRTail xi n := by
  have hxi1 : xi < 1 := by norm_num at hxi ⊢; linarith
  have hcontract := lrLowRTail_succ_le_mul hxi0 hxi1 n
  have hratio := lrLowAlpha_ratio_ge (n := n) (by omega)
  have hn78 : (7 / 8 : ℝ) ≤ (n : ℝ) / (n + 1) := by
    have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hxiRatio : xi ≤ lrLowAlphaRatio n := by
    unfold lrLowAlphaRatio
    norm_num at hxi ⊢
    linarith
  exact hcontract.trans (mul_le_mul_of_nonneg_right hxiRatio
    (lrLowRTail_nonneg hxi0 n))

end CourtadeKumar
