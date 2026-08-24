import InformationTheory.CourtadeKumar.RadialContactCurvature

/-! Transfer of contact curvature to radial perspective coordinates. -/

open Set

namespace CourtadeKumar

/-- The Hessian quadratic form after the perspective change
`(z,r) ↦ (m,u) = (z,r*z)`, evaluated at a radial stationary point. -/
noncomputable def radialPerspectiveDirectionalCurvature
    (rho theta z r dz dr : ℝ) : ℝ :=
  radialLagrangianDirectionalCurvature rho theta z r
      dz (r * dz + z * dr) / z

theorem perspectiveDirection_ne_zero
    {z r dz dr : ℝ}
    (hz : z ≠ 0) (hdir : dz ≠ 0 ∨ dr ≠ 0) :
    dz ≠ 0 ∨ r * dz + z * dr ≠ 0 := by
  by_cases hdz : dz = 0
  · right
    rw [hdz]
    simp only [mul_zero, zero_add]
    have hdr : dr ≠ 0 := by simpa [hdz] using hdir
    exact mul_ne_zero hz hdr
  · exact Or.inl hdz

/-- Positive definiteness survives the perspective coordinate change at a
stationary contact.  This replaces a determinant/Schur-complement calculation
by the injective linear map `(dz,dr) ↦ (dz,r*dz+z*dr)`. -/
theorem radialPerspectiveDirectionalCurvature_pos
    {rho theta z r dz dr : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hzhalf : z < 1 / 2)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0)
    (hdir : dz ≠ 0 ∨ dr ≠ 0) :
    0 < radialPerspectiveDirectionalCurvature rho theta z r dz dr := by
  unfold radialPerspectiveDirectionalCurvature
  exact div_pos
    (radialLagrangianDirectionalCurvature_pos hrho hr hz hzhalf hstat
      (perspectiveDirection_ne_zero hz.1.ne' hdir))
    hz.1

/-- In particular, the pure radial direction has positive perspective curvature. -/
theorem radialPerspectivePureRadialCurvature_pos
    {rho theta z r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hzhalf : z < 1 / 2)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0) :
    0 < radialPerspectiveDirectionalCurvature rho theta z r 0 1 :=
  radialPerspectiveDirectionalCurvature_pos hrho hr hz hzhalf hstat
    (Or.inr one_ne_zero)

end CourtadeKumar
