import InformationTheory.CourtadeKumar.RadialMidpointLogGap

/-! Monotonicity of the midpoint-gradient logarithmic ratio. -/

open Set

namespace CourtadeKumar

noncomputable def radialEulerMidpointLogRatio (c r z : ℝ) : ℝ :=
  Real.log (radialEulerLogArg c r z) /
    Real.log (radialEulerMassArg c r z)

theorem hasDerivAt_radialEulerMidpointLogRatio
    {c r z : ℝ}
    (hX : radialEulerLogArg c r z ≠ 0)
    (hY : radialEulerMassArg c r z ≠ 0)
    (hlogY : Real.log (radialEulerMassArg c r z) ≠ 0) :
    HasDerivAt (fun s ↦ radialEulerMidpointLogRatio s r z)
      (2 * c * r ^ 2 * z ^ 2 *
        (radialEulerLogArg c r z * Real.log (radialEulerLogArg c r z) -
          radialEulerMassArg c r z * Real.log (radialEulerMassArg c r z)) /
        (radialEulerLogArg c r z * radialEulerMassArg c r z *
          Real.log (radialEulerMassArg c r z) ^ 2)) c := by
  have hXinner : HasDerivAt (fun s : ℝ ↦ radialEulerLogArg s r z)
      (-2 * c * r ^ 2 * z ^ 2) c := by
    unfold radialEulerLogArg
    convert (hasDerivAt_const c ((1 - z) ^ 2)).sub
      (((hasDerivAt_id c).pow 2).const_mul (r ^ 2 * z ^ 2)) using 1
    · funext s
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      ring
    · simp only [id_eq]
      ring
  have hYinner : HasDerivAt (fun s : ℝ ↦ radialEulerMassArg s r z)
      (-2 * c * r ^ 2 * z ^ 2) c := by
    unfold radialEulerMassArg
    convert (hasDerivAt_const c (z ^ 2)).sub
      (((hasDerivAt_id c).pow 2).const_mul (r ^ 2 * z ^ 2)) using 1
    · funext s
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      ring
    · simp only [id_eq]
      ring
  have hlogX := (Real.hasDerivAt_log hX).comp c hXinner
  have hlogY' := (Real.hasDerivAt_log hY).comp c hYinner
  unfold radialEulerMidpointLogRatio
  convert hlogX.div hlogY' hlogY using 1
  simp only [Function.comp_apply]
  field_simp [hX, hY, hlogY]
  ring

theorem radialEulerMidpointLogRatio_deriv_pos_physical
    {c r z : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1)
    (hr : 0 < r) (hz : z ∈ Ioo (1 / 2 : ℝ) 1)
    (hupper : (1 + r) * z < 1) :
    0 < deriv (fun s ↦ radialEulerMidpointLogRatio s r z) c := by
  have hz0 : 0 < z := lt_trans (by norm_num) hz.1
  have hgap1 : 0 < 1 - z - r * z := by nlinarith [hupper]
  have hsum1 : 0 < 1 - z + r * z := by nlinarith
  have hX1 : 0 < radialEulerLogArg 1 r z := by
    unfold radialEulerLogArg
    nlinarith [mul_pos hgap1 hsum1]
  have hcle : c ^ 2 ≤ 1 := by
    have hcplus : 0 ≤ 1 + c := by linarith [hc.1]
    nlinarith [mul_nonneg (sub_nonneg.2 hc.2) hcplus]
  have hX : 0 < radialEulerLogArg c r z := by
    unfold radialEulerLogArg at hX1 ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hcle)
      (mul_nonneg (sq_nonneg r) (sq_nonneg z))]
  have hYeq := radialEulerMassArg_eq_logArg_add c r z
  have hY : 0 < radialEulerMassArg c r z := by
    rw [hYeq]
    nlinarith [hz.1]
  have hYlt : radialEulerMassArg c r z < 1 := by
    unfold radialEulerMassArg
    have hnonneg : 0 ≤ c ^ 2 * r ^ 2 * z ^ 2 := by positivity
    have hzsq : z ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.2 hz.2) (by linarith : 0 < 1 + z)]
    nlinarith
  have hlogY : Real.log (radialEulerMassArg c r z) ≠ 0 :=
    (Real.log_neg hY hYlt).ne
  rw [(hasDerivAt_radialEulerMidpointLogRatio
    hX.ne' hY.ne' hlogY).deriv]
  have hgap := radialEuler_mul_log_gap_pos hc.1 hr hz hX
  exact div_pos
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hc.1)
      (sq_pos_of_pos hr))
      (sq_pos_of_pos (lt_trans (by norm_num) hz.1))) hgap)
    (mul_pos (mul_pos hX hY) (sq_pos_of_ne_zero hlogY))

theorem radialEulerMidpointLogRatio_strictMonoOn_physical
    {r z : ℝ}
    (hr : 0 < r) (hz : z ∈ Ioo (1 / 2 : ℝ) 1)
    (hupper : (1 + r) * z < 1) :
    StrictMonoOn (fun c ↦ radialEulerMidpointLogRatio c r z)
      (Ioc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc (0 : ℝ) 1)
  · intro c hc
    have hz0 : 0 < z := lt_trans (by norm_num) hz.1
    have hgap1 : 0 < 1 - z - r * z := by nlinarith [hupper]
    have hsum1 : 0 < 1 - z + r * z := by nlinarith
    have hX1 : 0 < radialEulerLogArg 1 r z := by
      unfold radialEulerLogArg
      nlinarith [mul_pos hgap1 hsum1]
    have hcle : c ^ 2 ≤ 1 := by
      have hcplus : 0 ≤ 1 + c := by linarith [hc.1]
      nlinarith [mul_nonneg (sub_nonneg.2 hc.2) hcplus]
    have hX : 0 < radialEulerLogArg c r z := by
      unfold radialEulerLogArg at hX1 ⊢
      nlinarith [mul_nonneg (sub_nonneg.2 hcle)
        (mul_nonneg (sq_nonneg r) (sq_nonneg z))]
    have hY : 0 < radialEulerMassArg c r z := by
      rw [radialEulerMassArg_eq_logArg_add]
      nlinarith [hz.1]
    have hYlt : radialEulerMassArg c r z < 1 := by
      unfold radialEulerMassArg
      have hnonneg : 0 ≤ c ^ 2 * r ^ 2 * z ^ 2 := by positivity
      have hzsq : z ^ 2 < 1 := by
        nlinarith [mul_pos (sub_pos.2 hz.2) (by linarith : 0 < 1 + z)]
      nlinarith
    exact (hasDerivAt_radialEulerMidpointLogRatio hX.ne' hY.ne'
      (Real.log_neg hY hYlt).ne).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioc] at hc
    exact radialEulerMidpointLogRatio_deriv_pos_physical
      ⟨hc.1, hc.2.le⟩ hr hz hupper

theorem radialEulerMidpointLogRatio_rho_lt_one
    {rho r z : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (hz : z ∈ Ioo (1 / 2 : ℝ) 1)
    (hupper : (1 + r) * z < 1) :
    radialEulerMidpointLogRatio rho r z <
      radialEulerMidpointLogRatio 1 r z := by
  exact radialEulerMidpointLogRatio_strictMonoOn_physical hr hz hupper
    ⟨hrho.1, hrho.2.le⟩ ⟨zero_lt_one, le_rfl⟩ hrho.2

end CourtadeKumar
