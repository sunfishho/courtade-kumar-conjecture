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

end CourtadeKumar
