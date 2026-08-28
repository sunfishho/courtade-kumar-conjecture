import InformationTheory.CourtadeKumar.LRPositiveChartAssembly

/-!
# A gap-budget substitute for the positive-chart tangent certificate

The tangent reserve can be rewritten using the affine identity between the
outer midpoint and half-midpoint numerators.  Consequently, a lower bound
on the target gap closes the tangent reserve as soon as the half-midpoint
numerator is nonnegative.  This form is designed for the noncompact
`k >= 4` cancellation tail.
-/

open Set

namespace CourtadeKumar

/-- The amount by which the target gap exceeds the half-midpoint tangent
expenditure. -/
noncomputable def lrFlowGapBudget (R v t : ℝ) : ℝ :=
  lrFlowGap R v t -
    lrFlowHalfSlope R v * (lrFlowM v / 2)

/-- Exact decomposition of the tangent reserve into a half-midpoint term
and the new gap budget. -/
theorem lrFlowTReserve_eq_halfMidpoint_add_gapBudget
    (R v t : ℝ) :
    lrFlowTReserve R v t =
      lrFlowHalfSlope R v *
          lrFlowNumeratorP R (lrFlowM v / 2) v t +
        4 * lrWKernel R 1 * lrFlowJ R v t *
          lrFlowGapBudget R v t := by
  have hsub := lrFlowNumeratorP_sub R
    (lrFlowM v / 2) (lrFlowM v) v t
  rw [lrFlowH_eq_negJ] at hsub
  unfold lrFlowTReserve lrFlowGapBudget
  linear_combination lrFlowHalfSlope R v * hsub

/-- On the positive-`J` chart, a nonnegative half-midpoint numerator and a
nonnegative gap budget imply the full tangent certificate. -/
theorem lrFlowTReserve_nonneg_of_halfMidpoint_gapBudget
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrFlowJ R v t)
    (hhalf : 0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t)
    (hbudget : 0 ≤ lrFlowGapBudget R v t) :
    0 ≤ lrFlowTReserve R v t := by
  rw [lrFlowTReserve_eq_halfMidpoint_add_gapBudget]
  exact add_nonneg
    (mul_nonneg (lrFlowHalfSlope_pos hR hv).le hhalf)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (lrWKernel_one_pos hR).le)
        hJ.le)
      hbudget)

/-- The positive target-root chart can therefore use the gap budget in
place of a separately supplied tangent reserve. -/
theorem lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_gapBudget
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hJ : 0 < lrFlowJ R v t)
    (hhalf : 0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t)
    (hbudget : 0 ≤ lrFlowGapBudget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_T
    hR hp hv ht htarget hJ hhalf
      (lrFlowTReserve_nonneg_of_halfMidpoint_gapBudget
        hR hv hJ hhalf hbudget)

end CourtadeKumar
