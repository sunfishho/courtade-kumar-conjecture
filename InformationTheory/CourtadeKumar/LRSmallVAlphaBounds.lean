import InformationTheory.CourtadeKumar.LRLowShapeAlphaOrder

/-!
# Uniform Hausdorff-moment bounds for the small-odds chart

These are the two sequence estimates used by the analytic small-`v`
certificate.  The existing rational tail bounds give a direct kernel proof;
no numerical decision procedure is involved.
-/

namespace CourtadeKumar

theorem lrLowAlpha_succ_ge_half
    {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) * lrLowAlpha n ≤ lrLowAlpha (n + 1) := by
  have hpos := lrLowAlpha_pos n
  have hratio := lrLowAlpha_ratio_ge hn
  have hhalf : (1 / 2 : ℝ) ≤ (n : ℝ) / (n + 1) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (by positivity : (0 : ℝ) < n + 1)]
    nlinarith
  have hratioHalf : (1 / 2 : ℝ) ≤
      lrLowAlpha (n + 1) / lrLowAlpha n := hhalf.trans hratio
  exact (le_div_iff₀ hpos).mp hratioHalf

theorem lrLowAlpha_ge_rational (n : ℕ) :
    1 / (2 * (2 * (n : ℝ) + 1)) ≤ lrLowAlpha n := by
  rcases n with _ | n
  · norm_num [lrLowAlpha]
  · have hb := lrLowB_le_upper (n + 1)
    have hj : (0 : ℝ) ≤ n + 1 := by positivity
    have hupper :
        1 / (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1)) ≤
          1 - ((n + 1 : ℕ) : ℝ) * 4 * lrLowBUpper (n + 1) := by
      unfold lrLowBUpper
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      field_simp
      ring_nf
      nlinarith [sq_nonneg (n : ℝ), pow_nonneg hn 3]
    unfold lrLowAlpha lrLowCStar
    have hmul := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * 4)
    have hsub := sub_le_sub_left hmul 1
    exact hupper.trans (by simpa [mul_assoc] using hsub)

end CourtadeKumar
