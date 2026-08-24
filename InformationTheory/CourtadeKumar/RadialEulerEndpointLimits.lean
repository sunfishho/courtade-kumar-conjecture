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

/-- The uncontracted Euler logarithm diverges at the outer endpoint of a
nondegenerate ray. -/
theorem tendsto_radialEulerLog_one_outerEndpoint
    {r : ℝ} (hr : 0 < r) :
    Tendsto (radialEulerLog 1 r)
      (nhdsWithin (1 + r)⁻¹ (Iio (1 + r)⁻¹)) atTop := by
  let cap : ℝ := (1 + r)⁻¹
  let l : Filter ℝ := nhdsWithin cap (Iio cap)
  have h1r : 0 < 1 + r := by linarith
  have hcap : 0 < cap := by
    dsimp [cap]
    exact inv_pos.2 h1r
  have hargAt : radialEulerLogArg 1 r cap = 0 := by
    dsimp [cap]
    unfold radialEulerLogArg
    field_simp [h1r.ne']
    ring
  have hargContinuous : Continuous (radialEulerLogArg 1 r) := by
    unfold radialEulerLogArg
    fun_prop
  have hargNhds : Tendsto (radialEulerLogArg 1 r) l (nhds 0) := by
    rw [← hargAt]
    exact hargContinuous.continuousAt.mono_left inf_le_left
  have hzpos : ∀ᶠ z in l, 0 < z := by
    change Ioi 0 ∈ nhds cap ⊓ principal (Iio cap)
    exact mem_inf_of_left (Ioi_mem_nhds hcap)
  have hargPos : ∀ᶠ z in l, radialEulerLogArg 1 r z ∈ Ioi (0 : ℝ) := by
    filter_upwards [hzpos, self_mem_nhdsWithin] with z hz0 hzcap
    have hupper : (1 + r) * z < 1 := by
      have := mul_lt_mul_of_pos_left hzcap h1r
      dsimp [cap] at this
      simpa [h1r.ne'] using this
    exact (radialEulerLogArg_order_physical
      (rho := (0 : ℝ)) (r := r) (z := z)
      (by norm_num) hr hz0 hupper).1.1
  have hargTendsto : Tendsto (radialEulerLogArg 1 r) l
      (nhdsWithin 0 (Ioi (0 : ℝ))) :=
    tendsto_nhdsWithin_iff.2 ⟨hargNhds, hargPos⟩
  have hlog : Tendsto (fun z ↦ Real.log (radialEulerLogArg 1 r z)) l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hargTendsto
  change Tendsto (radialEulerLog 1 r) l atTop
  unfold radialEulerLog
  exact hlog.const_mul_atBot_of_neg (by norm_num)

/-- For a strict contraction, the numerator Euler logarithm remains finite
at the same outer endpoint. -/
theorem tendsto_radialEulerLog_contracted_outerEndpoint
    {rho r : ℝ} (hrho : rho ∈ Ico (0 : ℝ) 1) (hr : 0 < r) :
    Tendsto (radialEulerLog rho r)
      (nhdsWithin (1 + r)⁻¹ (Iio (1 + r)⁻¹))
      (nhds (radialEulerLog rho r (1 + r)⁻¹)) := by
  have h1r : 0 < 1 + r := by linarith
  have hrhoplus : 0 < 1 + rho := by linarith [hrho.1]
  have hrhosq : rho ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.2 hrho.2) hrhoplus]
  have harg : 0 < radialEulerLogArg rho r (1 + r)⁻¹ := by
    unfold radialEulerLogArg
    field_simp [h1r.ne']
    nlinarith [mul_pos (sub_pos.2 hrhosq) (sq_pos_of_pos hr)]
  exact (hasDerivAt_radialEulerLog harg.ne').continuousAt.mono_left inf_le_left

/-- The radial Euler ratio tends to zero at the open outer endpoint. -/
theorem tendsto_radialEulerLogRatio_outerEndpoint
    {rho r : ℝ} (hrho : rho ∈ Ico (0 : ℝ) 1) (hr : 0 < r) :
    Tendsto (radialEulerLogRatio rho r)
      (nhdsWithin (1 + r)⁻¹ (Iio (1 + r)⁻¹)) (nhds 0) := by
  unfold radialEulerLogRatio
  exact (tendsto_radialEulerLog_contracted_outerEndpoint hrho hr).div_atTop
    (tendsto_radialEulerLog_one_outerEndpoint hr)

end CourtadeKumar
