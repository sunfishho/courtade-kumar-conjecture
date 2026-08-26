import InformationTheory.CourtadeKumar.LRLowShapeAlphaOrder

/-!
# Ratio propagation for the low-shape `V` tail

Once the two auxiliary tails contract by the alpha ratio, this lemma propagates
nonnegativity from the entry coefficient at index seven to every later index.
It isolates the order-theoretic core of the manuscript's tail argument.
-/

namespace CourtadeKumar

noncomputable def lrLowAlphaRatio (n : ℕ) : ℝ :=
  lrLowAlpha (n + 1) / lrLowAlpha n

lemma lrLowAlphaRatio_nonneg (n : ℕ) : 0 ≤ lrLowAlphaRatio n := by
  unfold lrLowAlphaRatio
  exact div_nonneg (lrLowAlpha_pos (n + 1)).le (lrLowAlpha_pos n).le

lemma lrLowAlphaRatio_mul_alpha (n : ℕ) :
    lrLowAlphaRatio n * lrLowAlpha n = lrLowAlpha (n + 1) := by
  unfold lrLowAlphaRatio
  field_simp [(lrLowAlpha_pos n).ne']

lemma lrLowAlphaRatio_le_one
    {n : ℕ} (hn : 1 ≤ n) : lrLowAlphaRatio n ≤ 1 := by
  unfold lrLowAlphaRatio
  exact (lrLowAlpha_ratio_le_next hn).trans (by
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    linarith)

lemma lrLow_tail_step
    {L F Q R : ℕ → ℝ} {Vstar C delta G : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hFn : F n = C * lrLowAlpha n - delta * Q n - G * R n)
    (hFsucc : F (n + 1) =
      C * lrLowAlpha (n + 1) - delta * Q (n + 1) - G * R (n + 1))
    (hLn : L n = F n + Vstar)
    (hLsucc : L (n + 1) = F (n + 1) + Vstar)
    (hQ : Q (n + 1) ≤ lrLowAlphaRatio n * Q n)
    (hR : R (n + 1) ≤ lrLowAlphaRatio n * R n)
    (hdelta : 0 ≤ delta) (hG : 0 ≤ G) (hVstar : 0 ≤ Vstar)
    (hLnNonneg : 0 ≤ L n) :
    0 ≤ L (n + 1) := by
  have hrNonneg := lrLowAlphaRatio_nonneg n
  have hrOne := lrLowAlphaRatio_le_one hn
  have hAlpha := lrLowAlphaRatio_mul_alpha n
  have hVscale : lrLowAlphaRatio n * Vstar ≤ Vstar :=
    mul_le_of_le_one_left hVstar hrOne
  have hFstep : lrLowAlphaRatio n * F n ≤ F (n + 1) := by
    rw [hFn, hFsucc]
    calc
      lrLowAlphaRatio n *
            (C * lrLowAlpha n - delta * Q n - G * R n) =
          C * lrLowAlpha (n + 1) -
            delta * (lrLowAlphaRatio n * Q n) -
            G * (lrLowAlphaRatio n * R n) := by rw [← hAlpha]; ring
      _ ≤ C * lrLowAlpha (n + 1) - delta * Q (n + 1) -
          G * R (n + 1) := by
        gcongr
  have hLstep : lrLowAlphaRatio n * L n ≤ L (n + 1) := by
    rw [hLn, hLsucc]
    calc
      lrLowAlphaRatio n * (F n + Vstar) =
          lrLowAlphaRatio n * F n + lrLowAlphaRatio n * Vstar := by ring
      _ ≤ F (n + 1) + Vstar := by
        exact add_le_add hFstep hVscale
  exact (mul_nonneg hrNonneg hLnNonneg).trans hLstep

theorem lrLow_tail_propagation
    {L F Q R : ℕ → ℝ} {Vstar C delta G : ℝ}
    (hF : ∀ n, 7 ≤ n →
      F n = C * lrLowAlpha n - delta * Q n - G * R n)
    (hL : ∀ n, 7 ≤ n → L n = F n + Vstar)
    (hQ : ∀ n, 7 ≤ n → Q (n + 1) ≤ lrLowAlphaRatio n * Q n)
    (hR : ∀ n, 7 ≤ n → R (n + 1) ≤ lrLowAlphaRatio n * R n)
    (hdelta : 0 ≤ delta) (hG : 0 ≤ G) (hVstar : 0 ≤ Vstar)
    (hL7 : 0 ≤ L 7) :
    ∀ n, 7 ≤ n → 0 ≤ L n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hL7
  | succ n hn ih =>
      exact lrLow_tail_step (by omega)
        (hF n hn) (hF (n + 1) (by omega))
        (hL n hn) (hL (n + 1) (by omega))
        (hQ n hn) (hR n hn) hdelta hG hVstar ih

end CourtadeKumar
