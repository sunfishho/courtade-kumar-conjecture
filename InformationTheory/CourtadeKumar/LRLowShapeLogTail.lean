import InformationTheory.CourtadeKumar.LRLowShapeRTail

/-!
# Logarithmic tails used in `Q_n`

The series is proved summable by comparison with a geometric series.  We also
record its exact one-step recursion and the geometric tail bound used at the
entry index seven.
-/

namespace CourtadeKumar

noncomputable def lrLowLogTail (xi : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, xi ^ (k + n) / ((k + n : ℕ) : ℝ)

lemma lrLowLogTail_term_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 ≤ xi ^ (k + n) / ((k + n : ℕ) : ℝ) := by
  positivity

lemma summable_lrLowLogTail
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun k : ℕ ↦ xi ^ (k + n) / ((k + n : ℕ) : ℝ)) := by
  let g : ℕ → ℝ := fun k ↦ (xi ^ n / (n : ℝ)) * xi ^ k
  have hg : Summable g :=
    (summable_geometric_of_lt_one hxi0 hxi1).mul_left (xi ^ n / (n : ℝ))
  apply Summable.of_nonneg_of_le
    (fun k ↦ lrLowLogTail_term_nonneg hxi0 hn k) _ hg
  intro k
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hknR : (0 : ℝ) < k + n := by positivity
  have hden : (n : ℝ) ≤ ((k + n : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ k + n by omega)
  have hpow : 0 ≤ xi ^ (k + n) := pow_nonneg hxi0 _
  calc
    xi ^ (k + n) / ((k + n : ℕ) : ℝ)
        ≤ xi ^ (k + n) / (n : ℝ) := by
          exact div_le_div_of_nonneg_left hpow hnR hden
    _ = g k := by
      dsimp [g]
      rw [show k + n = n + k by omega, pow_add]
      ring

lemma lrLowLogTail_nonneg
    {xi : ℝ} (hxi : 0 ≤ xi) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowLogTail xi n := by
  unfold lrLowLogTail
  exact tsum_nonneg (fun k ↦ lrLowLogTail_term_nonneg hxi hn k)

lemma lrLowLogTail_recursion
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowLogTail xi n = xi ^ n / (n : ℝ) + lrLowLogTail xi (n + 1) := by
  unfold lrLowLogTail
  rw [(summable_lrLowLogTail hxi0 hxi1 hn).tsum_eq_zero_add]
  congr 1
  · simp
  · apply tsum_congr
    intro k
    congr 2 <;> omega

lemma lrLowLogTail_le_geometric
    {xi : ℝ} (hxi0 : 0 ≤ xi) (hxi1 : xi < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowLogTail xi n ≤ xi ^ n / ((n : ℝ) * (1 - xi)) := by
  let g : ℕ → ℝ := fun k ↦ (xi ^ n / (n : ℝ)) * xi ^ k
  have hg : HasSum g ((xi ^ n / (n : ℝ)) / (1 - xi)) := by
    exact (hasSum_geometric_of_lt_one hxi0 hxi1).mul_left (xi ^ n / (n : ℝ))
  have hs := summable_lrLowLogTail hxi0 hxi1 hn
  unfold lrLowLogTail
  calc
    ∑' k : ℕ, xi ^ (k + n) / ((k + n : ℕ) : ℝ)
        ≤ ∑' k : ℕ, g k := hs.tsum_le_tsum (fun k ↦ by
          have hnR : (0 : ℝ) < n := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
          have hden : (n : ℝ) ≤ ((k + n : ℕ) : ℝ) := by
            exact_mod_cast (show n ≤ k + n by omega)
          calc
            xi ^ (k + n) / ((k + n : ℕ) : ℝ)
                ≤ xi ^ (k + n) / (n : ℝ) := by
                  exact div_le_div_of_nonneg_left (pow_nonneg hxi0 _) hnR hden
            _ = g k := by
              dsimp [g]
              rw [show k + n = n + k by omega, pow_add]
              ring) hg.summable
    _ = (xi ^ n / (n : ℝ)) / (1 - xi) := hg.tsum_eq
    _ = xi ^ n / ((n : ℝ) * (1 - xi)) := by rw [div_div]

end CourtadeKumar
