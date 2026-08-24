import InformationTheory.CourtadeKumar.RadialContactConstruction

/-! Endpoint limits of the radial Euler ratio. -/

open Set Filter

namespace CourtadeKumar

/-- Every closed Euler logarithm has first-order behavior `z` at the origin. -/
theorem tendsto_radialEulerLog_div_zero_right (c r : ℝ) :
    Tendsto (fun z : ℝ ↦ radialEulerLog c r z / z)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hderiv : HasDerivAt (radialEulerLog c r) 1 0 := by
    convert hasDerivAt_radialEulerLog
      (c := c) (r := r) (z := (0 : ℝ)) (by simp [radialEulerLogArg]) using 1 <;>
      simp [radialEulerLog, radialEulerLogArg, radialEulerLogDeriv]
  simpa [radialEulerLog, radialEulerLogArg, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero_right

/-- Consequently the radial Euler ratio tends to one at the open origin. -/
theorem tendsto_radialEulerLogRatio_zero_right (rho r : ℝ) :
    Tendsto (radialEulerLogRatio rho r)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hR := tendsto_radialEulerLog_div_zero_right rho r
  have h1 := tendsto_radialEulerLog_div_zero_right 1 r
  have hquot := hR.div h1 (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      ((fun z : ℝ ↦ radialEulerLog rho r z / z) /
        (fun z : ℝ ↦ radialEulerLog 1 r z / z))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by simpa using hquot
  apply hquot'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  unfold radialEulerLogRatio
  have hzpos : 0 < z := hz
  exact div_div_div_cancel_right₀ hzpos.ne' _ _

end CourtadeKumar
