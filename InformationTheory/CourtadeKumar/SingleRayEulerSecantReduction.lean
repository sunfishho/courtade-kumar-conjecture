import InformationTheory.CourtadeKumar.SingleRayEulerSecant

/-! Exact reduction of the corrected reserve to an Euler-ratio secant budget. -/

open Set
open scoped NNReal

namespace CourtadeKumar

noncomputable def singleRayEulerSlopeBudget
    (rho M r z : ℝ) : ℝ :=
  (radialNatEntropyRatio rho r M - lowerRayNatEnvelope rho M / M) /
    (radialNatEntropyRatio 1 r M - radialNatEntropyRatio 1 r z)

noncomputable def singleRayEulerSlopeDenom
    (rho M r : ℝ) : ℝ :=
  topR rho * radialNatEntropy 1 r M -
    4 * topEll rho * M * singleRayContactDenom M r

noncomputable def singleRayClosedEulerSlopeBudget
    (rho M r : ℝ) : ℝ :=
  (radialNatEntropy rho r M - lowerRayNatEnvelope rho M) /
    singleRayEulerSlopeDenom rho M r

lemma strictRayContact_upper
    {r z : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    z < (1 + r)⁻¹ := by
  rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hr.1] : 0 < 1 + r)]
  calc
    z * (1 + r) < z * 2 :=
      mul_lt_mul_of_pos_left (by linarith [hr.2]) hz.1
    _ < 1 := by linarith [hz.2]

lemma radialNatEntropyRatio_one_loss_pos
    {r M z : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    0 < radialNatEntropyRatio 1 r M - radialNatEntropyRatio 1 r z := by
  have hMdom : M ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM, hMz.trans hzupper⟩
  have hzdom : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.trans hMz, hzupper⟩
  have hbits := strictAntiOn_radialEntropyRatio hr hMdom hzdom hMz
  rw [radialNatEntropyRatio_one_eq_bits,
    radialNatEntropyRatio_one_eq_bits]
  simpa [mul_sub] using
    mul_pos (Real.log_pos one_lt_two) (sub_pos.mpr hbits)

theorem singleRayEulerSlopeDenom_eq_mass_mul_inputLoss_of_contact
    {rho M r z : ℝ} (hM : M ≠ 0) (hz : z ≠ 0)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayEulerSlopeDenom rho M r =
      M * (radialNatEntropyRatio 1 r M -
        radialNatEntropyRatio 1 r z) := by
  have hexplicit := singleRayNatContact_explicit hcontact
  unfold singleRayContactDenom topS topR at hexplicit
  unfold singleRayEulerSlopeDenom radialNatEntropyRatio
    singleRayContactDenom topR
  field_simp [hz] at hexplicit
  field_simp [hM, hz]
  linear_combination hexplicit

theorem singleRayEulerSlopeDenom_pos_of_contact
    {rho M r z : ℝ}
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    0 < singleRayEulerSlopeDenom rho M r := by
  rw [singleRayEulerSlopeDenom_eq_mass_mul_inputLoss_of_contact
    hM.1.ne' hz.1.ne' hcontact]
  exact mul_pos hM.1 (radialNatEntropyRatio_one_loss_pos
    hr hM.1 hMz (strictRayContact_upper hr hz))

theorem singleRayEulerSlopeBudget_eq_closed_of_contact
    {rho M r z : ℝ}
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayEulerSlopeBudget rho M r z =
      singleRayClosedEulerSlopeBudget rho M r := by
  have hden := singleRayEulerSlopeDenom_pos_of_contact
    hM hr hz hMz hcontact
  have hdenEq := singleRayEulerSlopeDenom_eq_mass_mul_inputLoss_of_contact
    hM.1.ne' hz.1.ne' hcontact
  unfold singleRayEulerSlopeBudget singleRayClosedEulerSlopeBudget
  rw [hdenEq]
  unfold radialNatEntropyRatio
  field_simp [hM.1.ne', hden.ne']

theorem singleRayEulerSlopeBudget_nonneg
    {alpha : ℝ≥0} {M r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z) :
    0 ≤ singleRayEulerSlopeBudget
      (channelRho (alpha : ℝ)) M r z := by
  have hzupper := strictRayContact_upper hr hz
  have hden := radialNatEntropyRatio_one_loss_pos
    hr hM.1 hMz hzupper
  have hbit := bellmanEnvelope_le_radialChannelEntropy
    halpha ⟨hr.1.le, hr.2.le⟩ ⟨hM.1.le, hM.2.le⟩
  have hnat : lowerRayNatEnvelope (channelRho (alpha : ℝ)) M ≤
      radialNatEntropy (channelRho (alpha : ℝ)) r M := by
    rw [lowerRayNatEnvelope_eq_bellman]
    calc
      Real.log 2 * bellmanEnvelope (alpha : ℝ) M ≤
          Real.log 2 * radialTriangleChannelEntropy alpha r M :=
        mul_le_mul_of_nonneg_left hbit (Real.log_pos one_lt_two).le
      _ = radialNatEntropy (channelRho (alpha : ℝ)) r M := by
        rw [radialTriangleChannelEntropy_eq_nat]
        field_simp [log_two_ne_zero]
  unfold singleRayEulerSlopeBudget radialNatEntropyRatio
  exact div_nonneg
    ((div_le_div_iff_of_pos_right hM.1).2 hnat |> sub_nonneg.mpr)
    hden.le

/-- At every strict physical contact there is an intermediate mass where
the corrected reserve is nonnegative exactly when the Euler ratio lies
below the explicit secant budget. -/
theorem exists_eulerRatio_le_budget_iff_correctedReserve
    {rho M r z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hMz : M < z)
    (hcontact : M / z * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    ∃ ξ ∈ Ioo M z,
      (0 ≤ singleRayCorrectedReserve rho M r z (M / z) ↔
        radialEulerRatio rho r ξ ≤
          singleRayEulerSlopeBudget rho M r z) := by
  have hzupper := strictRayContact_upper hr hz
  obtain ⟨ξ, hξ, hsecant⟩ := exists_radialEulerRatio_eq_ratioLoss
    hrho hr hM.1 hMz hzupper
  have hinput := radialNatEntropyRatio_one_loss_pos
    hr hM.1 hMz hzupper
  have hcz : M = M / z * z := by field_simp [hz.1.ne']
  have hreserve :=
    singleRayCorrectedReserve_eq_mass_mul_outputRatioGap_of_contact
      hM.1.ne' hz.1.ne' hcz hcontact
  refine ⟨ξ, hξ, ?_⟩
  rw [hreserve, mul_nonneg_iff_of_pos_left hM.1]
  change (0 ≤ radialNatEntropyRatio rho r z -
      lowerRayNatEnvelope rho M / M) ↔ _
  rw [← hsecant]
  unfold singleRayEulerSlopeBudget
  rw [div_le_div_iff_of_pos_right hinput]
  constructor <;> intro h <;> linarith

end CourtadeKumar
