import InformationTheory.CourtadeKumar.CanonicalRadialProfileDerivative

/-! Differentiation of the natural-triangle gradient along curved paths. -/

open Set

namespace CourtadeKumar

noncomputable def scaledNatEntropyNegBilinear
    (c p u x y dx dy : ℝ) : ℝ :=
  ((x - c * y) * (dx - c * dy) /
      ((p - c * u) * (1 - (p - c * u))) +
    (x + c * y) * (dx + c * dy) /
      ((p + c * u) * (1 - (p + c * u)))) / 2

noncomputable def naturalTriangleDirectionalBilinear
    (rho theta p u x y dx dy : ℝ) : ℝ :=
  theta * scaledNatEntropyNegBilinear 1 p u x y dx dy -
    scaledNatEntropyNegBilinear rho p u x y dx dy

noncomputable def naturalTriangleHessianBilinear
    (rho theta p u x y dx dy : ℝ) : ℝ :=
  naturalTriangleKmm rho theta p u * x * dx +
    naturalTriangleKmu rho theta p u * (x * dy + y * dx) +
    naturalTriangleKuu rho theta p u * y * dy

theorem naturalTriangleDirectionalBilinear_eq_hessian
    (rho theta p u x y dx dy : ℝ) :
    naturalTriangleDirectionalBilinear rho theta p u x y dx dy =
      naturalTriangleHessianBilinear rho theta p u x y dx dy := by
  unfold naturalTriangleHessianBilinear naturalTriangleKmu
    naturalTriangleKmm naturalTriangleKuu
  unfold naturalTriangleDirectionalCurvature
    naturalTriangleDirectionalBilinear scaledNatEntropyNegCurvature
    scaledNatEntropyNegBilinear
  ring

theorem hasDerivAt_scaledNatEntropyDirectionalFirst_comp
    {c x y : ℝ} {p u : ℝ → ℝ} {dp du t : ℝ}
    (hp : HasDerivAt p dp t)
    (hu : HasDerivAt u du t)
    (hminus : p t - c * u t ∈ Ioo (0 : ℝ) 1)
    (hplus : p t + c * u t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s ↦ scaledNatEntropyDirectionalFirst c (p s) (u s) x y 0)
      (-scaledNatEntropyNegBilinear c (p t) (u t) x y dp du) t := by
  have hargMinus : HasDerivAt (fun s ↦ p s - c * u s) (dp - c * du) t := by
    simpa using hp.sub (hu.const_mul c)
  have hargPlus : HasDerivAt (fun s ↦ p s + c * u s) (dp + c * du) t := by
    simpa using hp.add (hu.const_mul c)
  have hsMinus := (hasDerivAt_natEntropySlope
    hminus.1.ne' hminus.2.ne).comp t hargMinus
  have hsPlus := (hasDerivAt_natEntropySlope
    hplus.1.ne' hplus.2.ne).comp t hargPlus
  have hm := hsMinus.const_mul (x - c * y)
  have hq := hsPlus.const_mul (x + c * y)
  unfold scaledNatEntropyDirectionalFirst scaledNatEntropyNegBilinear
  convert (hm.add hq).div_const 2 using 1
  · funext s
    simp
  · field_simp [hminus.1.ne', hminus.2.ne,
      hplus.1.ne', hplus.2.ne]
    ring

theorem hasDerivAt_naturalTriangleDirectionalFirst_comp
    {rho theta x y : ℝ} {p u : ℝ → ℝ} {dp du t : ℝ}
    (hp : HasDerivAt p dp t)
    (hu : HasDerivAt u du t)
    (hRminus : p t - rho * u t ∈ Ioo (0 : ℝ) 1)
    (hRplus : p t + rho * u t ∈ Ioo (0 : ℝ) 1)
    (hminus : p t - u t ∈ Ioo (0 : ℝ) 1)
    (hplus : p t + u t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s ↦ naturalTriangleDirectionalFirst rho theta
        (p s) (u s) x y 0)
      (naturalTriangleDirectionalBilinear rho theta
        (p t) (u t) x y dp du) t := by
  have hR := hasDerivAt_scaledNatEntropyDirectionalFirst_comp
    (c := rho) (x := x) (y := y) hp hu hRminus hRplus
  have h1 := hasDerivAt_scaledNatEntropyDirectionalFirst_comp
    (c := (1 : ℝ)) (x := x) (y := y) hp hu
    (by simpa using hminus) (by simpa using hplus)
  unfold naturalTriangleDirectionalFirst naturalTriangleDirectionalBilinear
  convert hR.sub (h1.const_mul theta) using 1
  ring

theorem hasDerivAt_naturalTriangleKm_comp
    {rho theta : ℝ} {p u : ℝ → ℝ} {dp du t : ℝ}
    (hp : HasDerivAt p dp t)
    (hu : HasDerivAt u du t)
    (hRminus : p t - rho * u t ∈ Ioo (0 : ℝ) 1)
    (hRplus : p t + rho * u t ∈ Ioo (0 : ℝ) 1)
    (hminus : p t - u t ∈ Ioo (0 : ℝ) 1)
    (hplus : p t + u t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ naturalTriangleKm rho theta (p s) (u s))
      (naturalTriangleKmm rho theta (p t) (u t) * dp +
        naturalTriangleKmu rho theta (p t) (u t) * du) t := by
  have h := hasDerivAt_naturalTriangleDirectionalFirst_comp
    (rho := rho) (theta := theta) (x := (1 : ℝ)) (y := (0 : ℝ))
    hp hu hRminus hRplus hminus hplus
  unfold naturalTriangleKm
  convert h using 1
  rw [naturalTriangleDirectionalBilinear_eq_hessian]
  unfold naturalTriangleHessianBilinear
  ring

theorem hasDerivAt_naturalTriangleKu_comp
    {rho theta : ℝ} {p u : ℝ → ℝ} {dp du t : ℝ}
    (hp : HasDerivAt p dp t)
    (hu : HasDerivAt u du t)
    (hRminus : p t - rho * u t ∈ Ioo (0 : ℝ) 1)
    (hRplus : p t + rho * u t ∈ Ioo (0 : ℝ) 1)
    (hminus : p t - u t ∈ Ioo (0 : ℝ) 1)
    (hplus : p t + u t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ naturalTriangleKu rho theta (p s) (u s))
      (naturalTriangleKmu rho theta (p t) (u t) * dp +
        naturalTriangleKuu rho theta (p t) (u t) * du) t := by
  have h := hasDerivAt_naturalTriangleDirectionalFirst_comp
    (rho := rho) (theta := theta) (x := (0 : ℝ)) (y := (1 : ℝ))
    hp hu hRminus hRplus hminus hplus
  unfold naturalTriangleKu
  convert h using 1
  rw [naturalTriangleDirectionalBilinear_eq_hessian]
  unfold naturalTriangleHessianBilinear
  ring

end CourtadeKumar
