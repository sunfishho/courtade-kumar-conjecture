import InformationTheory.CourtadeKumar.PerspectiveSecondVariation

/-! First and second directional derivatives of the natural-unit triangle Lagrangian. -/

open Set

namespace CourtadeKumar

noncomputable def naturalTriangleLagrangian
    (rho theta p u : ℝ) : ℝ :=
  scaledNatEntropy rho p u - theta * scaledNatEntropy 1 p u

noncomputable def naturalTriangleLagrangianAlong
    (rho theta p u x y t : ℝ) : ℝ :=
  naturalTriangleLagrangian rho theta (p + t * x) (u + t * y)

noncomputable def naturalTriangleDirectionalFirst
    (rho theta p u x y t : ℝ) : ℝ :=
  scaledNatEntropyDirectionalFirst rho p u x y t -
    theta * scaledNatEntropyDirectionalFirst 1 p u x y t

noncomputable def naturalTriangleKm
    (rho theta p u : ℝ) : ℝ :=
  naturalTriangleDirectionalFirst rho theta p u 1 0 0

noncomputable def naturalTriangleKu
    (rho theta p u : ℝ) : ℝ :=
  naturalTriangleDirectionalFirst rho theta p u 0 1 0

noncomputable def naturalTriangleDirectionalCurvature
    (rho theta p u x y : ℝ) : ℝ :=
  theta * scaledNatEntropyNegCurvature 1 p u x y -
    scaledNatEntropyNegCurvature rho p u x y

theorem hasDerivAt_naturalTriangleLagrangianAlong
    {rho theta p u x y t : ℝ}
    (hRminus : p + t * x - rho * (u + t * y) ∈ Ioo (0 : ℝ) 1)
    (hRplus : p + t * x + rho * (u + t * y) ∈ Ioo (0 : ℝ) 1)
    (hminus : p + t * x - (u + t * y) ∈ Ioo (0 : ℝ) 1)
    (hplus : p + t * x + (u + t * y) ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (naturalTriangleLagrangianAlong rho theta p u x y)
      (naturalTriangleDirectionalFirst rho theta p u x y t) t := by
  have hR := hasDerivAt_scaledNatEntropyAlong hRminus hRplus
  have h1 := hasDerivAt_scaledNatEntropyAlong
    (c := (1 : ℝ)) (by simpa using hminus) (by simpa using hplus)
  unfold naturalTriangleLagrangianAlong naturalTriangleLagrangian
    naturalTriangleDirectionalFirst
  convert hR.sub (h1.const_mul theta) using 1

theorem hasDerivAt_naturalTriangleDirectionalFirst
    {rho theta p u x y : ℝ}
    (hRminus : p - rho * u ∈ Ioo (0 : ℝ) 1)
    (hRplus : p + rho * u ∈ Ioo (0 : ℝ) 1)
    (hminus : p - u ∈ Ioo (0 : ℝ) 1)
    (hplus : p + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (naturalTriangleDirectionalFirst rho theta p u x y)
      (naturalTriangleDirectionalCurvature rho theta p u x y) 0 := by
  have hR := hasDerivAt_scaledNatEntropyDirectionalFirst
    (c := rho) (p := p) (u := u) (x := x) (y := y) hRminus hRplus
  have h1 := hasDerivAt_scaledNatEntropyDirectionalFirst
    (c := (1 : ℝ)) (p := p) (u := u) (x := x) (y := y)
    (by simpa using hminus) (by simpa using hplus)
  unfold naturalTriangleDirectionalFirst naturalTriangleDirectionalCurvature
  convert hR.sub (h1.const_mul theta) using 1
  ring

theorem naturalTriangleDirectionalCurvature_radial
    (rho theta z r x y : ℝ) :
    naturalTriangleDirectionalCurvature rho theta z (r * z) x y =
      radialLagrangianDirectionalCurvature rho theta z r x y := by
  unfold naturalTriangleDirectionalCurvature radialLagrangianDirectionalCurvature
  rfl

theorem naturalTriangleDirectionalFirst_eq_gradient
    (rho theta p u x y : ℝ) :
    naturalTriangleDirectionalFirst rho theta p u x y 0 =
      naturalTriangleKm rho theta p u * x +
        naturalTriangleKu rho theta p u * y := by
  unfold naturalTriangleKm naturalTriangleKu
  unfold naturalTriangleDirectionalFirst scaledNatEntropyDirectionalFirst
  ring

theorem scaledNatEntropy_euler_defect
    (c r z : ℝ) :
    scaledNatEntropy c z (r * z) -
        z * (naturalTriangleDirectionalFirst c 0 z (r * z) 1 0 0 +
          r * naturalTriangleDirectionalFirst c 0 z (r * z) 0 1 0) =
      radialEulerDefect c r z := by
  unfold naturalTriangleDirectionalFirst scaledNatEntropyDirectionalFirst
    scaledNatEntropy radialEulerDefect radialNatEntropy radialNatEntropyDeriv
    natEntropySlope
  ring

/-- The Euler stationarity equation is exactly the perspective identity
`k = z (k_m + r k_u)`. -/
theorem naturalTriangleLagrangian_euler_at_stationary
    {rho theta r z : ℝ}
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0) :
    naturalTriangleLagrangian rho theta z (r * z) =
      z * (naturalTriangleKm rho theta z (r * z) +
        r * naturalTriangleKu rho theta z (r * z)) := by
  have hR := scaledNatEntropy_euler_defect rho r z
  have h1 := scaledNatEntropy_euler_defect 1 r z
  have hReq : scaledNatEntropy rho z (r * z) =
      z * (naturalTriangleDirectionalFirst rho 0 z (r * z) 1 0 0 +
        r * naturalTriangleDirectionalFirst rho 0 z (r * z) 0 1 0) +
        radialEulerDefect rho r z := by linarith
  have h1eq : scaledNatEntropy 1 z (r * z) =
      z * (naturalTriangleDirectionalFirst 1 0 z (r * z) 1 0 0 +
        r * naturalTriangleDirectionalFirst 1 0 z (r * z) 0 1 0) +
        radialEulerDefect 1 r z := by linarith
  have hzero : radialEulerDefect rho r z -
      theta * radialEulerDefect 1 r z = 0 := by linarith
  unfold naturalTriangleLagrangian naturalTriangleKm naturalTriangleKu
  rw [hReq, h1eq]
  unfold naturalTriangleDirectionalFirst
  rw [show radialEulerDefect rho r z =
      theta * radialEulerDefect 1 r z by linarith]
  ring

end CourtadeKumar
