import InformationTheory.CourtadeKumar.LRSmallVAlphaBounds

/-!
# Middle coefficients in the analytic small-odds certificate

This proves the sign estimate corresponding to equation (101) of the
small-`v` proof.  It covers every coefficient strictly between the two
potentially adverse locations.
-/

namespace CourtadeKumar

theorem lrLowAlpha_antitone : Antitone lrLowAlpha := by
  intro j n hjn
  have hscaled := lrLowB_scaled_monotone hjn
  unfold lrLowAlpha lrLowCStar
  nlinarith

theorem lrSmallV_middle_brace_nonneg
    {v : ℝ} {n m : ℕ}
    (hv0 : 0 ≤ v) (hv : v ≤ 1 / 3)
    (hm : 2 ≤ m) (hmn : m < n) :
    0 ≤ v * (lrLowAlpha n - lrLowAlpha (n - m)) +
      (m : ℝ) / (m - 1) * lrLowAlpha (n - m + 1) := by
  have hj : 1 ≤ n - m := by omega
  have haj : 0 < lrLowAlpha (n - m) := lrLowAlpha_pos _
  have han : 0 ≤ lrLowAlpha n := (lrLowAlpha_pos _).le
  have hhalf := lrLowAlpha_succ_ge_half hj
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hratio : (1 : ℝ) ≤ (m : ℝ) / (m - 1) := by
    rw [le_div_iff₀ hden]
    linarith
  have hsucc : 0 ≤ lrLowAlpha (n - m + 1) :=
    (lrLowAlpha_pos _).le
  have hratioTerm : lrLowAlpha (n - m + 1) ≤
      (m : ℝ) / (m - 1) * lrLowAlpha (n - m + 1) := by
    nlinarith
  have hfirst : -v * lrLowAlpha (n - m) ≤
      v * (lrLowAlpha n - lrLowAlpha (n - m)) := by
    nlinarith [mul_nonneg hv0 han]
  have hpay : 0 ≤ -v * lrLowAlpha (n - m) +
      (1 / 2 : ℝ) * lrLowAlpha (n - m) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) haj.le]
  linarith

end CourtadeKumar
