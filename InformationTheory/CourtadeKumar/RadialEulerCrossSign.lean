import InformationTheory.CourtadeKumar.RadialLogFraction

/-! Transfer of the logarithmic-fraction monotonicity to the Euler core. -/

open Set

namespace CourtadeKumar

theorem log_cross_neg_of_lt
    {q x y : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) q)
    (hy : y ∈ Ioo (0 : ℝ) q)
    (hxy : x < y) :
    y * (q - x) * Real.log y - x * (q - y) * Real.log x < 0 := by
  have hmono := radialLogFraction_strictMonoOn hq hx hy hxy
  unfold radialLogFraction at hmono
  have hqx : 0 < q - x := sub_pos.2 hx.2
  have hqy : 0 < q - y := sub_pos.2 hy.2
  rw [div_lt_div_iff₀ hqx hqy] at hmono
  simp only [Real.negMulLog_def] at hmono
  nlinarith

theorem radialEulerSlopeNumerator_eq_arg_gap_div
    {c r z : ℝ} (hz : z ≠ 0) :
    radialEulerSlopeNumerator c r z =
      ((1 - z) - radialEulerLogArg c r z) / z := by
  unfold radialEulerSlopeNumerator radialEulerLogArg
  field_simp [hz]
  ring

theorem radialEulerCrossCore_eq_logCross_div
    {rho r z : ℝ} (hz : z ≠ 0) :
    radialEulerCrossCore rho r z =
      (radialEulerLogArg rho r z *
          ((1 - z) - radialEulerLogArg 1 r z) *
          Real.log (radialEulerLogArg rho r z) -
        radialEulerLogArg 1 r z *
          ((1 - z) - radialEulerLogArg rho r z) *
          Real.log (radialEulerLogArg 1 r z)) / z := by
  unfold radialEulerCrossCore
  rw [radialEulerSlopeNumerator_eq_arg_gap_div hz,
    radialEulerSlopeNumerator_eq_arg_gap_div hz]
  field_simp [hz]

/-- Abstract physical-domain version of the radial cross sign. The remaining
work is only to verify the four displayed order hypotheses from the triangle
parameters. -/
theorem radialEulerCrossCore_neg_of_arg_order
    {rho r z : ℝ}
    (hz : 0 < z)
    (hq : 1 - z ∈ Ioo (0 : ℝ) 1)
    (harg1 : radialEulerLogArg 1 r z ∈ Ioo (0 : ℝ) (1 - z))
    (hargR : radialEulerLogArg rho r z ∈ Ioo (0 : ℝ) (1 - z))
    (horder : radialEulerLogArg 1 r z < radialEulerLogArg rho r z) :
    radialEulerCrossCore rho r z < 0 := by
  rw [radialEulerCrossCore_eq_logCross_div hz.ne']
  exact div_neg_of_neg_of_pos
    (log_cross_neg_of_lt hq harg1 hargR horder) hz

end CourtadeKumar
