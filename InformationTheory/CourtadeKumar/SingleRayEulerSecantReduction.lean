import InformationTheory.CourtadeKumar.SingleRayEulerSecant

/-! Exact reduction of the corrected reserve to an Euler-ratio secant budget. -/

open Set

namespace CourtadeKumar

noncomputable def singleRayEulerSlopeBudget
    (rho M r z : ℝ) : ℝ :=
  (radialNatEntropyRatio rho r M - lowerRayNatEnvelope rho M / M) /
    (radialNatEntropyRatio 1 r M - radialNatEntropyRatio 1 r z)

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
