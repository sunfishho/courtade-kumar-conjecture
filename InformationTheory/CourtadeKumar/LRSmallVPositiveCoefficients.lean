import InformationTheory.CourtadeKumar.LRSmallVEntryComparison

/-!
# All positive-index small-odds coefficients

The index-two entry comparison and the small-odds tail propagation give every
comparison `ℒₙ`, `n ≥ 2`.  The exact coefficient reduction then proves all
convolution coefficients of positive index.
-/

open Set

namespace CourtadeKumar

theorem lrLowVComparison_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ n : ℕ, 2 ≤ n →
      0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) n := by
  exact lrLowVComparison_nonneg_tail_smallV_of_two hv hvSmall ht
    (lrLowVComparison_two_nonneg_smallV hv hvSmall ht)

theorem lrLowVConvolutionCoeff_posIndex_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowVConvolutionCoeff v t n := by
  have hid := lrLowVConvolutionCoeff_pred_eq_comparison
    (v := v) (t := t) ht.1.le (n := n + 1) (by omega)
  rw [show n + 1 - 1 = n by omega] at hid
  rw [hid]
  exact add_nonneg
    (lrLowVComparison_nonneg_smallV hv hvSmall ht (n + 1) (by omega))
    (mul_nonneg
      (mul_nonneg (by positivity) (lrFlowA_pos hv ht).le)
      (lrLowP_nonneg hv.1.le (sq_nonneg t) (n + 1)))

end CourtadeKumar
