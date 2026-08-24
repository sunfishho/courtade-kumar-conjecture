import InformationTheory.CourtadeKumar.RadialEulerCrossCore

/-! Normalized base-plus-shape coordinates for the radial Euler logarithm. -/

namespace CourtadeKumar

noncomputable def radialEulerBase (z : ℝ) : ℝ :=
  -Real.log (1 - z)

noncomputable def radialEulerShape (w : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (1 - w)

noncomputable def radialEulerShapeVariable (c r z : ℝ) : ℝ :=
  (c * r * z / (1 - z)) ^ 2

theorem radialEulerLogArg_factor
    {c r z : ℝ} (hbase : 1 - z ≠ 0) :
    radialEulerLogArg c r z =
      (1 - z) ^ 2 * (1 - radialEulerShapeVariable c r z) := by
  unfold radialEulerLogArg radialEulerShapeVariable
  field_simp [hbase]

/-- The closed Euler logarithm is a common base term plus a one-variable
shape term. This is the coordinate system used by the elasticity proof. -/
theorem radialEulerLog_eq_base_add_shape
    {c r z : ℝ}
    (hbase : 1 - z ≠ 0)
    (hshape : 1 - radialEulerShapeVariable c r z ≠ 0) :
    radialEulerLog c r z =
      radialEulerBase z + radialEulerShape (radialEulerShapeVariable c r z) := by
  unfold radialEulerLog radialEulerBase radialEulerShape
  rw [radialEulerLogArg_factor hbase]
  rw [Real.log_mul (pow_ne_zero 2 hbase) hshape, Real.log_pow]
  ring

theorem radialEulerShapeVariable_scale
    {c r z : ℝ} :
    radialEulerShapeVariable c r z =
      c ^ 2 * radialEulerShapeVariable 1 r z := by
  unfold radialEulerShapeVariable
  ring

end CourtadeKumar
