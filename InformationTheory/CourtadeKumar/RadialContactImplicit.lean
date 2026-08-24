import InformationTheory.CourtadeKumar.RadialContactNondegeneracy
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Local implicit-function setup for the canonical radial contact. -/

namespace CourtadeKumar

noncomputable def radialEulerImplicitEquation
    (rho theta : ℝ) (x : ℝ × ℝ) : ℝ :=
  radialEulerLogRatio rho x.1 x.2 - theta

theorem contDiffAt_radialEulerImplicitEquation
    {n : WithTop ℕ∞} {rho theta r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0)
    (hden : radialEulerLog 1 r z ≠ 0) :
    ContDiffAt ℝ n (radialEulerImplicitEquation rho theta) (r, z) := by
  have hargRcd : ContDiffAt ℝ n
      (fun x : ℝ × ℝ ↦ radialEulerLogArg rho x.1 x.2) (r, z) := by
    unfold radialEulerLogArg
    fun_prop
  have harg1cd : ContDiffAt ℝ n
      (fun x : ℝ × ℝ ↦ radialEulerLogArg 1 x.1 x.2) (r, z) := by
    unfold radialEulerLogArg
    fun_prop
  have hlogR : ContDiffAt ℝ n
      (fun x : ℝ × ℝ ↦ radialEulerLog rho x.1 x.2) (r, z) := by
    unfold radialEulerLog
    exact contDiffAt_const.mul (hargRcd.log hargR)
  have hlog1 : ContDiffAt ℝ n
      (fun x : ℝ × ℝ ↦ radialEulerLog 1 x.1 x.2) (r, z) := by
    unfold radialEulerLog
    exact contDiffAt_const.mul (harg1cd.log harg1)
  unfold radialEulerImplicitEquation radialEulerLogRatio
  exact (hlogR.div hlog1 hden).sub contDiffAt_const

noncomputable def radialEulerImplicitDerivative
    (rho theta r z : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (radialEulerImplicitEquation rho theta) (r, z)

/-- The smooth radial Euler equation, together with a nonzero contact
derivative, satisfies Mathlib's implicit-function hypotheses. -/
theorem isContDiffImplicitAt_radialEulerEquation
    {rho theta r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0)
    (hden : radialEulerLog 1 r z ≠ 0)
    (hcontact : deriv (radialEulerLogRatio rho r) z ≠ 0) :
    IsContDiffImplicitAt (2 : WithTop ℕ∞)
      (radialEulerImplicitEquation rho theta)
      (radialEulerImplicitDerivative rho theta r z) (r, z) := by
  let f := radialEulerImplicitEquation rho theta
  let f' := radialEulerImplicitDerivative rho theta r z
  have hcont : ContDiffAt ℝ (2 : WithTop ℕ∞) f (r, z) :=
    contDiffAt_radialEulerImplicitEquation hargR harg1 hden
  have hf : HasFDerivAt f f' (r, z) := by
    exact hcont.differentiableAt two_ne_zero |>.hasFDerivAt
  let g : ℝ →L[ℝ] ℝ :=
    f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)
  have hline : HasFDerivAt (fun w : ℝ ↦ (r, w))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) z := by
    fun_prop
  have hgF : HasFDerivAt (fun w : ℝ ↦ f (r, w)) g z := by
    exact hf.comp z hline
  have hg : HasDerivAt (fun w : ℝ ↦ f (r, w)) (g 1) z :=
    hasFDerivAt_iff_hasDerivAt.mp hgF
  have hknown : HasDerivAt (fun w : ℝ ↦ f (r, w))
      (deriv (radialEulerLogRatio rho r) z) z := by
    have hratio := hasDerivAt_radialEulerLogRatio hargR harg1 hden
    unfold f radialEulerImplicitEquation
    convert hratio.sub_const theta using 1
    exact hratio.deriv
  have hg1 : g 1 = deriv (radialEulerLogRatio rho r) z := hg.unique hknown
  have hg_apply (y : ℝ) : g y = y * deriv (radialEulerLogRatio rho r) z := by
    calc
      g y = y • g 1 := by
        rw [← map_smul]
        simp
      _ = y * deriv (radialEulerLogRatio rho r) z := by
        rw [hg1]
        rfl
  have hg_bijective : Function.Bijective g := by
    constructor
    · intro x y hxy
      rw [hg_apply x, hg_apply y] at hxy
      exact mul_right_cancel₀ hcontact hxy
    · intro y
      refine ⟨y / deriv (radialEulerLogRatio rho r) z, ?_⟩
      rw [hg_apply]
      exact div_mul_cancel₀ y hcontact
  exact ⟨hf, hcont, hg_bijective, two_ne_zero⟩

/-- A nondegenerate radial Euler contact lies on a local `C²` solution
branch of the contact equation. -/
theorem exists_localContDiff_radialContact
    {rho theta r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0)
    (hden : radialEulerLog 1 r z ≠ 0)
    (hcontact : deriv (radialEulerLogRatio rho r) z ≠ 0)
    (hroot : radialEulerLogRatio rho r z = theta) :
    ∃ φ : ℝ → ℝ,
      ContDiffAt ℝ (2 : WithTop ℕ∞) φ r ∧
      φ r = z ∧
      ∀ᶠ s in nhds r, radialEulerLogRatio rho s (φ s) = theta := by
  let h := isContDiffImplicitAt_radialEulerEquation
    (theta := theta) hargR harg1 hden hcontact
  let φ : ℝ → ℝ := h.implicitFunction
  refine ⟨φ, h.contDiffAt_implicitFunction, ?_, ?_⟩
  · have hself := h.eventually_implicitFunction_apply_eq.self_of_nhds
    exact hself rfl
  · filter_upwards [h.apply_implicitFunction] with s hs
    change radialEulerLogRatio rho s (φ s) - theta =
      radialEulerLogRatio rho r z - theta at hs
    rw [hroot] at hs
    linarith

end CourtadeKumar
