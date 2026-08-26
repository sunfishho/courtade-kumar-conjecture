import InformationTheory.CourtadeKumar.LRSmallVFarTail

/-!
# Assembly of the exceptional small-odds coefficient payment

This combines the geometric decay `v^(2n) ≤ v²/9^(n-1)` with the
rational tail estimate and the uniform lower bound for `αₙ`.  It is the
kernel-checked content of equations (103)--(104).
-/

namespace CourtadeKumar

lemma lrSmallV_even_power_decay
    {v : ℝ} {n : ℕ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 3)
    (hn : 1 ≤ n) :
    v ^ (2 * n) ≤ v ^ 2 / 9 ^ (n - 1) := by
  have hvSq : v ^ 2 ≤ (1 / 9 : ℝ) := by nlinarith [sq_nonneg v]
  have hvSqNonneg : 0 ≤ v ^ 2 := sq_nonneg v
  have hpow := pow_le_pow_left₀ hvSqNonneg hvSq (n - 1)
  have hsplit : 2 * n = 2 + 2 * (n - 1) := by omega
  rw [hsplit, pow_add, show v ^ (2 * (n - 1)) = (v ^ 2) ^ (n - 1) by
    rw [← pow_mul]]
  have hmul := mul_le_mul_of_nonneg_left hpow hvSqNonneg
  calc
    v ^ 2 * (v ^ 2) ^ (n - 1)
        ≤ v ^ 2 * (1 / 9 : ℝ) ^ (n - 1) := hmul
    _ = v ^ 2 / 9 ^ (n - 1) := by
      rw [one_div, inv_pow]
      ring

theorem lrSmallV_adverse_coefficients_paid
    {v : ℝ} {n : ℕ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 3)
    (hn : 3 ≤ n) :
    v ^ (2 * n) *
        (1 / (2 * (n : ℝ)) + 13 / (72 * ((n : ℝ) + 1))) ≤
      3 * v ^ 2 / (32 * (2 * (n : ℝ) + 1)) := by
  have hdecay := lrSmallV_even_power_decay hv0 hv (by omega : 1 ≤ n)
  have htail := lrSmallV_adverse_tail_bound hn
  have hbracket :
      0 ≤ (1 : ℝ) / (2 * n) + 13 / (72 * (n + 1)) := by
    positivity
  have hvSq : 0 ≤ v ^ 2 := sq_nonneg v
  have hfirst := mul_le_mul_of_nonneg_right hdecay hbracket
  have hsecond := mul_le_mul_of_nonneg_left htail hvSq
  calc
    v ^ (2 * n) *
          (1 / (2 * (n : ℝ)) + 13 / (72 * ((n : ℝ) + 1)))
        ≤ v ^ 2 / 9 ^ (n - 1) *
          (1 / (2 * (n : ℝ)) + 13 / (72 * ((n : ℝ) + 1))) := hfirst
    _ = v ^ 2 * ((1 / 9 ^ (n - 1)) *
          (1 / (2 * (n : ℝ)) + 13 / (72 * ((n : ℝ) + 1)))) := by ring
    _ ≤ v ^ 2 * (3 / (32 * (2 * (n : ℝ) + 1))) := hsecond
    _ = 3 * v ^ 2 / (32 * (2 * (n : ℝ) + 1)) := by ring

theorem lrSmallV_first_coefficient_pays
    {v : ℝ} (n : ℕ) :
    3 * v ^ 2 / (32 * (2 * (n : ℝ) + 1)) ≤
      3 * v ^ 2 * lrLowAlpha n / 16 := by
  have halpha := lrLowAlpha_ge_rational n
  have hscale : 0 ≤ 3 * v ^ 2 / 16 := by positivity
  have hmul := mul_le_mul_of_nonneg_left halpha hscale
  have hden : (2 * (2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  convert hmul using 1 <;> field_simp [hden] <;> ring

end CourtadeKumar
