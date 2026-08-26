import InformationTheory.CourtadeKumar.LRSmallVAdverseAssembly

/-!
# The two exceptional index-two coefficients

The general payment argument starts at `n = 3`.  These two strict rational
estimates discharge the `n = 2` coefficient and its first tail successor.
-/

namespace CourtadeKumar

theorem lrSmallV_index_two_brace_pos :
    0 < 2 * lrLowAlpha 1 - (1 - lrLowAlpha 2) / 3 := by
  have ha1 := lrLowAlpha_ge_rational 1
  have ha2 := lrLowAlpha_ge_rational 2
  norm_num at ha1 ha2 ⊢
  linarith

theorem lrSmallV_index_three_brace_pos
    {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 3) :
    0 < (3 / 4 : ℝ) - v * (7 / 4 - lrLowAlpha 2) := by
  have ha2 : 0 < lrLowAlpha 2 := lrLowAlpha_pos 2
  have hfactor : 7 / 4 - lrLowAlpha 2 < (7 / 4 : ℝ) := by linarith
  by_cases hvz : v = 0
  · subst v
    norm_num
  · have hvpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvz)
    have hmul' := mul_lt_mul_of_pos_left hfactor hvpos
    have hvBound := mul_le_mul_of_nonneg_right hv
      (show (0 : ℝ) ≤ 7 / 4 by norm_num)
    nlinarith

end CourtadeKumar
