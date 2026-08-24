import InformationTheory.CourtadeKumar.RadialLagrangianHessian

/-! Actual Lagrangian Hessian entries and stationary perspective second variation. -/

open Set

namespace CourtadeKumar

noncomputable def naturalTriangleKmm
    (rho theta p u : ℝ) : ℝ :=
  naturalTriangleDirectionalCurvature rho theta p u 1 0

noncomputable def naturalTriangleKuu
    (rho theta p u : ℝ) : ℝ :=
  naturalTriangleDirectionalCurvature rho theta p u 0 1

noncomputable def naturalTriangleKmu
    (rho theta p u : ℝ) : ℝ :=
  (naturalTriangleDirectionalCurvature rho theta p u 1 1 -
    naturalTriangleKmm rho theta p u - naturalTriangleKuu rho theta p u) / 2

theorem naturalTriangle_hessianQuadratic
    (rho theta p u x y : ℝ) :
    hessianQuadratic (naturalTriangleKmm rho theta p u)
        (naturalTriangleKmu rho theta p u)
        (naturalTriangleKuu rho theta p u) x y =
      naturalTriangleDirectionalCurvature rho theta p u x y := by
  unfold naturalTriangleKmu
  unfold hessianQuadratic naturalTriangleKmm naturalTriangleKuu
  unfold naturalTriangleDirectionalCurvature scaledNatEntropyNegCurvature
  ring

/-- The complete second-variation expression of the stationary radial
perspective is positive in every nonzero perspective direction. -/
theorem radialStationaryPerspectiveSecondVariation_pos
    {rho theta z r dz dr : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hzhalf : z < 1 / 2)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0)
    (hdir : dz ≠ 0 ∨ dr ≠ 0) :
    0 < quotientSecondVariation
      (naturalTriangleLagrangian rho theta z (r * z))
      (affinePathFirstVariation
        (naturalTriangleKm rho theta z (r * z))
        (naturalTriangleKu rho theta z (r * z)) z r dz dr)
      (affinePathSecondVariation
        (naturalTriangleKu rho theta z (r * z))
        (naturalTriangleKmm rho theta z (r * z))
        (naturalTriangleKmu rho theta z (r * z))
        (naturalTriangleKuu rho theta z (r * z)) z r dz dr)
      z dz := by
  apply perspectiveSecondVariation_pos hz.1
    (naturalTriangleLagrangian_euler_at_stationary hstat) hdir
  intro x y hxy
  rw [naturalTriangle_hessianQuadratic]
  rw [naturalTriangleDirectionalCurvature_radial]
  exact radialLagrangianDirectionalCurvature_pos hrho hr hz hzhalf hstat hxy

end CourtadeKumar
