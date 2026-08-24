import InformationTheory.CourtadeKumar.RadialEulerNormalized

/-! The elementary monotonicity inequality behind the radial Euler sign. -/

open Set

namespace CourtadeKumar

noncomputable def radialLogFraction (q x : ℝ) : ℝ :=
  Real.negMulLog x / (q - x)

noncomputable def radialLogFractionDeriv (q x : ℝ) : ℝ :=
  (q * (-Real.log x - 1) + x) / (q - x) ^ 2

theorem hasDerivAt_radialLogFraction
    {q x : ℝ} (hx : x ≠ 0) (hqx : q - x ≠ 0) :
    HasDerivAt (radialLogFraction q) (radialLogFractionDeriv q x) x := by
  have hnum := Real.hasDerivAt_negMulLog hx
  have hden : HasDerivAt (fun y : ℝ => q - y) (-1) x := by
    convert (hasDerivAt_const x q).sub (hasDerivAt_id x) using 1 <;> ring
  unfold radialLogFraction radialLogFractionDeriv
  convert hnum.div hden hqx using 1
  field_simp [hqx]
  simp [Real.negMulLog_def]
  ring

theorem radialLogFractionDeriv_pos
    {q x : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) q) :
    0 < radialLogFractionDeriv q x := by
  have ht : 0 < x / q := div_pos hx.1 hq.1
  have hxt : x < x / q := by
    rw [lt_div_iff₀ hq.1]
    nlinarith [mul_pos hx.1 (sub_pos.2 hq.2)]
  have hloglt : Real.log x < Real.log (x / q) :=
    Real.log_lt_log hx.1 hxt
  have hlogle : Real.log (x / q) ≤ x / q - 1 :=
    Real.log_le_sub_one_of_pos ht
  have hbracket : 0 < -Real.log x - 1 + x / q := by
    linarith
  have halg : q * (-Real.log x - 1) + x =
      q * (-Real.log x - 1 + x / q) := by
    field_simp [hq.1.ne']
  have hnum : 0 < q * (-Real.log x - 1) + x := by
    rw [halg]
    exact mul_pos hq.1 hbracket
  unfold radialLogFractionDeriv
  exact div_pos hnum (sq_pos_of_ne_zero (sub_ne_zero.2 hx.2.ne'))

theorem radialLogFraction_strictMonoOn
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (radialLogFraction q) (Ioo (0 : ℝ) q) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) q)
  · intro x hx
    exact (hasDerivAt_radialLogFraction hx.1.ne'
      (sub_ne_zero.2 hx.2.ne')).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_radialLogFraction hx.1.ne'
      (sub_ne_zero.2 hx.2.ne')).deriv]
    exact radialLogFractionDeriv_pos hq hx

end CourtadeKumar
