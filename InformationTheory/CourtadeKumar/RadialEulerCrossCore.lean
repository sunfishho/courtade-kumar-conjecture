import InformationTheory.CourtadeKumar.RadialEulerRatioDerivative

/-! A denominator-free form of the radial Euler-ratio sign certificate. -/

namespace CourtadeKumar

/-- The polynomial coefficient appearing in the derivative of the closed
Euler logarithm. -/
noncomputable def radialEulerSlopeNumerator (c r z : ℝ) : ℝ :=
  1 - z + c ^ 2 * r ^ 2 * z

/-- The cross-numerator after clearing the two positive logarithm arguments
and the harmless factor `2`. -/
noncomputable def radialEulerCrossCore (rho r z : ℝ) : ℝ :=
  radialEulerLogArg rho r z * radialEulerSlopeNumerator 1 r z *
      Real.log (radialEulerLogArg rho r z) -
    radialEulerLogArg 1 r z * radialEulerSlopeNumerator rho r z *
      Real.log (radialEulerLogArg 1 r z)

theorem radialEulerLogDeriv_eq_slope_div
    {c r z : ℝ} :
    radialEulerLogDeriv c r z =
      radialEulerSlopeNumerator c r z / radialEulerLogArg c r z := by
  rfl

/-- Exact common-denominator identity for the ratio cross-numerator. -/
theorem radialEulerRatioCrossNumerator_eq_core_div
    {rho r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0) :
    radialEulerRatioCrossNumerator rho r z =
      radialEulerCrossCore rho r z /
        (2 * radialEulerLogArg rho r z * radialEulerLogArg 1 r z) := by
  unfold radialEulerRatioCrossNumerator radialEulerLogDeriv radialEulerLog
    radialEulerCrossCore radialEulerSlopeNumerator
  field_simp [hargR, harg1]
  ring

/-- On the physical domain, the denominator-cleared core has exactly the
same sign as the derivative cross-numerator. -/
theorem radialEulerRatioCrossNumerator_lt_zero_iff_core
    {rho r z : ℝ}
    (hargR : 0 < radialEulerLogArg rho r z)
    (harg1 : 0 < radialEulerLogArg 1 r z) :
    radialEulerRatioCrossNumerator rho r z < 0 ↔
      radialEulerCrossCore rho r z < 0 := by
  rw [radialEulerRatioCrossNumerator_eq_core_div hargR.ne' harg1.ne']
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge
      (div_nonneg (le_of_not_gt hn)
        (mul_nonneg (mul_nonneg (by norm_num) hargR.le) harg1.le))) h
  · intro h
    exact div_neg_of_neg_of_pos h
      (mul_pos (mul_pos (by norm_num) hargR) harg1)

end CourtadeKumar
