import InformationTheory.CourtadeKumar.SingleRayCorrectedReserve

/-! Gain-ratio form of the corrected strict single-ray reserve. -/

open Set

namespace CourtadeKumar

noncomputable def radialNatChannelGain (rho r z : ℝ) : ℝ :=
  radialNatEntropy rho r z - radialNatEntropy 1 r z

noncomputable def radialNatChannelGainRatio (rho r z : ℝ) : ℝ :=
  radialNatChannelGain rho r z / z

noncomputable def singleRayGainRatioThreshold (rho M r : ℝ) : ℝ :=
  topS rho * (Real.binEntropy M - radialNatEntropy 1 r M) / M +
    4 * topEll rho * M * r ^ 2

theorem hasDerivAt_radialNatChannelGainRatio
    {rho r z : ℝ} (hz : z ≠ 0)
    (hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatChannelGainRatio rho r)
      ((radialEulerDefect 1 r z - radialEulerDefect rho r z) / z ^ 2) z := by
  have hR := hasDerivAt_radialNatEntropy hRminus hRplus
  have h1 := hasDerivAt_radialNatEntropy
    (c := (1 : ℝ)) (by simpa using hminus) (by simpa using hplus)
  have hgain := hR.sub h1
  have hquot := hgain.div (hasDerivAt_id z) hz
  unfold radialNatChannelGainRatio radialNatChannelGain radialEulerDefect
  convert hquot using 1 <;> simp only [id_eq, Pi.sub_apply] <;>
    field_simp [hz] <;> ring

theorem radialNatChannelGainRatio_deriv_eq_eulerFactor
    {rho r z : ℝ}
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    (radialEulerDefect 1 r z - radialEulerDefect rho r z) / z ^ 2 =
      (1 - radialEulerRatio rho r z) *
        radialEulerDefect 1 r z / z ^ 2 := by
  have hden : radialEulerDefect 1 r z ≠ 0 :=
    (radialEulerDefect_pos (by simpa using hminus)
      (by simpa using hplus)).ne'
  unfold radialEulerRatio
  field_simp [hden]

theorem hasDerivAt_radialNatChannelGainRatio_eulerFactor
    {rho r z : ℝ} (hz : z ≠ 0)
    (hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatChannelGainRatio rho r)
      ((1 - radialEulerRatio rho r z) *
        radialEulerDefect 1 r z / z ^ 2) z := by
  rw [← radialNatChannelGainRatio_deriv_eq_eulerFactor hminus hplus]
  exact hasDerivAt_radialNatChannelGainRatio hz hRminus hRplus hminus hplus

theorem singleRayCorrectedReserve_eq_gain_form (rho M r z c : ℝ) :
    singleRayCorrectedReserve rho M r z c =
      c * radialNatChannelGain rho r z -
        topS rho * (Real.binEntropy M - radialNatEntropy 1 r M) -
          4 * topEll rho * M ^ 2 * r ^ 2 := by
  unfold singleRayCorrectedReserve radialNatEntropyQuadraticExcess
    radialNatChannelGain
  ring

/-- After imposing the perspective identity `c=M/z`, the corrected reserve
is a positive mass times one scalar gain-ratio gap. -/
theorem singleRayCorrectedReserve_eq_mass_mul_gainRatioGap
    {rho M r z : ℝ} (hM : M ≠ 0) (hz : z ≠ 0) :
    singleRayCorrectedReserve rho M r z (M / z) =
      M * (radialNatChannelGainRatio rho r z -
        singleRayGainRatioThreshold rho M r) := by
  rw [singleRayCorrectedReserve_eq_gain_form]
  unfold radialNatChannelGainRatio singleRayGainRatioThreshold
  field_simp [hM, hz]
  ring

theorem singleRayCorrectedReserve_nonneg_iff_gainRatio
    {rho M r z : ℝ} (hM : 0 < M) (hz : z ≠ 0) :
    0 ≤ singleRayCorrectedReserve rho M r z (M / z) ↔
      singleRayGainRatioThreshold rho M r ≤
        radialNatChannelGainRatio rho r z := by
  rw [singleRayCorrectedReserve_eq_mass_mul_gainRatioGap hM.ne' hz]
  rw [mul_nonneg_iff_of_pos_left hM]
  exact sub_nonneg

/-- The contact equation identifies the threshold as the gap between the
Bellman-envelope ratio at `M` and the input-entropy ratio at `z`. -/
theorem singleRayGainRatioThreshold_eq_envelopeRatio_sub_inputRatio_of_contact
    {rho M r z c : ℝ} (hM : M ≠ 0) (hz : z ≠ 0)
    (hcz : M = c * z)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayGainRatioThreshold rho M r =
      lowerRayNatEnvelope rho M / M - radialNatEntropy 1 r z / z := by
  have hexplicit := singleRayNatContact_explicit hcontact
  unfold singleRayContactDenom at hexplicit
  unfold singleRayGainRatioThreshold lowerRayNatEnvelope
  field_simp [hM, hz]
  linear_combination z * hexplicit +
    (radialNatEntropy 1 r z) * hcz

/-- Thus the corrected reserve is exactly the mass-scaled gap between the
output-entropy ratio and the Bellman-envelope ratio. -/
theorem singleRayCorrectedReserve_eq_mass_mul_outputRatioGap_of_contact
    {rho M r z c : ℝ} (hM : M ≠ 0) (hz : z ≠ 0)
    (hcz : M = c * z)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayCorrectedReserve rho M r z c =
      M * (radialNatEntropy rho r z / z -
        lowerRayNatEnvelope rho M / M) := by
  have hc : c = M / z := by
    rw [hcz]
    field_simp [hz]
  subst c
  have hcz' : M = M / z * z := by field_simp [hz]
  rw [singleRayCorrectedReserve_eq_mass_mul_gainRatioGap hM hz]
  rw [singleRayGainRatioThreshold_eq_envelopeRatio_sub_inputRatio_of_contact
    hM hz hcz' hcontact]
  unfold radialNatChannelGainRatio radialNatChannelGain
  ring

/-- Radial channel gain per unit mass increases under outward scaling.
This is the quotient form of entropy-scaling-surplus contraction. -/
theorem radialNatChannelGainRatio_le_of_le
    {rho r x y : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hx : 0 < x) (hxy : x < y)
    (hminus : (1 - r) * y ∈ Icc (0 : ℝ) 1)
    (hplus : (1 + r) * y ∈ Icc (0 : ℝ) 1) :
    radialNatChannelGainRatio rho r x ≤
      radialNatChannelGainRatio rho r y := by
  let c : ℝ := x / y
  have hy : 0 < y := hx.trans hxy
  have hc : c ∈ Ioo (0 : ℝ) 1 := by
    dsimp [c]
    exact ⟨div_pos hx hy, (div_lt_one hy).2 hxy⟩
  have hscale := radialNatEntropy_scalingDeficit_contraction
    hc hrho hminus hplus
  have hcy : c * y = x := by
    dsimp [c]
    field_simp [hy.ne']
  rw [hcy] at hscale
  unfold radialNatChannelGainRatio radialNatChannelGain
  rw [div_le_div_iff₀ hx hy]
  dsimp [c] at hscale
  field_simp [hy.ne'] at hscale
  linarith

theorem monotoneOn_radialNatChannelGainRatio
    {rho r U : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1) (hU : 0 < U)
    (hminus : (1 - r) * U ∈ Icc (0 : ℝ) 1)
    (hplus : (1 + r) * U ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (radialNatChannelGainRatio rho r) (Ioc (0 : ℝ) U) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy'
  · exact le_rfl
  · have hminusY : (1 - r) * y ∈ Icc (0 : ℝ) 1 := by
      have hfactor : 0 ≤ 1 - r := by
        by_contra hneg
        have : (1 - r) * U < 0 := mul_neg_of_neg_of_pos
          (lt_of_not_ge hneg) hU
        linarith [hminus.1]
      constructor
      · exact mul_nonneg hfactor hy.1.le
      · exact (mul_le_mul_of_nonneg_left hy.2 hfactor).trans hminus.2
    have hplusY : (1 + r) * y ∈ Icc (0 : ℝ) 1 := by
      have hfactor : 0 ≤ 1 + r := by
        by_contra hneg
        have : (1 + r) * U < 0 := mul_neg_of_neg_of_pos
          (lt_of_not_ge hneg) hU
        linarith [hplus.1]
      constructor
      · exact mul_nonneg hfactor hy.1.le
      · exact (mul_le_mul_of_nonneg_left hy.2 hfactor).trans hplus.2
    exact radialNatChannelGainRatio_le_of_le hrho hx.1 hxy'
      hminusY hplusY

end CourtadeKumar
