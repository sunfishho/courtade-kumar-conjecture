import InformationTheory.CourtadeKumar.LRSmallVMiddleCoefficients

/-!
# Uniform payment of the two adverse small-odds coefficients

This is the rational tail estimate in equation (104).  It shows that the
positive first coefficient has enough mass to absorb both exceptional tail
locations for every `n ≥ 3`.
-/

namespace CourtadeKumar

theorem lrSmallV_adverse_tail_bound
    {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / 9 ^ (n - 1) *
        (1 / (2 * (n : ℝ)) + 13 / (72 * ((n : ℝ) + 1))) ≤
      3 / (32 * (2 * (n : ℝ) + 1)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : 2 ≤ n - 1 := by omega
  have hpow : (81 : ℝ) ≤ 9 ^ (n - 1) := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 9 by norm_num) hexp
    norm_num at h ⊢
    exact h
  have hpowPos : (0 : ℝ) < 81 := by norm_num
  have hinvpow : (1 : ℝ) / 9 ^ (n - 1) ≤ 1 / 81 :=
    one_div_le_one_div_of_le hpowPos hpow
  have hnPos : (0 : ℝ) < n := by linarith
  have hnOnePos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbracket :
      (1 : ℝ) / (2 * n) + 13 / (72 * (n + 1)) ≤
        49 / (72 * n) := by
    field_simp [hnPos.ne', hnOnePos.ne']
    nlinarith
  have hbracketNonneg :
      0 ≤ (1 : ℝ) / (2 * n) + 13 / (72 * (n + 1)) := by
    positivity
  have hinvNonneg : (0 : ℝ) ≤ 1 / 81 := by norm_num
  calc
    (1 : ℝ) / 9 ^ (n - 1) *
          (1 / (2 * (n : ℝ)) + 13 / (72 * ((n : ℝ) + 1)))
        ≤ (1 / 81 : ℝ) * (49 / (72 * n)) :=
      mul_le_mul hinvpow hbracket hbracketNonneg hinvNonneg
    _ ≤ 3 / (32 * (2 * (n : ℝ) + 1)) := by
      have hden : (0 : ℝ) < 2 * n + 1 := by positivity
      field_simp [hnPos.ne', hden.ne']
      nlinarith

end CourtadeKumar
