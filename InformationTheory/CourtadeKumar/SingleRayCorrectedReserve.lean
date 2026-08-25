import InformationTheory.CourtadeKumar.EntropyDropQuadraticScaling

/-! The strict single-ray residual after extracting quadratic entropy contraction. -/

open Set

namespace CourtadeKumar

/-- The amount by which radial channel entropy gain exceeds the universal
quadratic-contraction lower bound. -/
noncomputable def radialNatEntropyQuadraticExcess
    (rho r z : ℝ) : ℝ :=
  radialNatEntropy rho r z - radialNatEntropy 1 r z -
    topS rho * (Real.binEntropy z - radialNatEntropy 1 r z)

/-- The corrected strict reserve left after the contact equation removes
the Bellman coefficient.  Unlike the bare quadratic lower bound, this
retains the channel-curvature excess needed near the ray boundary. -/
noncomputable def singleRayCorrectedReserve
    (rho M r z c : ℝ) : ℝ :=
  c * radialNatEntropyQuadraticExcess rho r z +
    topS rho *
      (c * (Real.binEntropy z - radialNatEntropy 1 r z) -
        (Real.binEntropy M - radialNatEntropy 1 r M)) -
    4 * topEll rho * M ^ 2 * r ^ 2

theorem radialNatEntropyQuadraticExcess_nonneg
    {rho r z : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    0 ≤ radialNatEntropyQuadraticExcess rho r z := by
  unfold radialNatEntropyQuadraticExcess
  exact sub_nonneg.mpr (radialNatEntropy_gain_ge_topS_mul_drop hrho hr hz)

/-- On the entropy-contact surface, the pure residual is exactly the
positive contact denominator times the corrected strict reserve. -/
theorem singleRayEntropyResidual_eq_denom_mul_correctedReserve_of_contact
    {rho M r z c : ℝ}
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayEntropyResidual rho M r z c =
      singleRayContactDenom M r *
        singleRayCorrectedReserve rho M r z c := by
  have hexplicit := singleRayNatContact_explicit hcontact
  unfold singleRayEntropyResidual singleRayCorrectedReserve
    radialNatEntropyQuadraticExcess singleRayContactDenom
  linear_combination -M * r ^ 2 * hexplicit

/-- Nonnegativity of the corrected reserve closes the pure-entropy
residual on the physical strict domain. -/
theorem singleRayEntropyResidual_nonneg_of_correctedReserve
    {rho M r z c : ℝ}
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2)
    (hreserve : 0 ≤ singleRayCorrectedReserve rho M r z c) :
    0 ≤ singleRayEntropyResidual rho M r z c := by
  rw [singleRayEntropyResidual_eq_denom_mul_correctedReserve_of_contact
    hcontact]
  exact mul_nonneg (singleRayContactDenom_pos hM hr).le hreserve

theorem singleRayEntropyResidual_nonneg_iff_correctedReserve
    {rho M r z c : ℝ}
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    0 ≤ singleRayEntropyResidual rho M r z c ↔
      0 ≤ singleRayCorrectedReserve rho M r z c := by
  rw [singleRayEntropyResidual_eq_denom_mul_correctedReserve_of_contact
    hcontact]
  exact mul_nonneg_iff_of_pos_left (singleRayContactDenom_pos hM hr)

/-- The corrected reserve is not a relaxation: on contact it is exactly
the previously obtained local-plus-scaling decomposition. -/
theorem singleRayCorrectedReserve_eq_local_add_scalingReserve
    {rho M r z c : ℝ}
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hcz : M = c * z)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayCorrectedReserve rho M r z c =
      singleRayNatLocalGap rho M r +
        singleRayNatScalingReserve rho c r z := by
  have hresidual :=
    singleRayEntropyResidual_eq_denom_mul_correctedReserve_of_contact hcontact
  have hgap := singleRayContactDenom_mul_gap_eq_entropyResidual hcontact
  have hdecomp := singleRayNatGap_eq_local_add_scalingReserve hcz hcontact
  have hden := singleRayContactDenom_pos hM hr
  have hmul : singleRayContactDenom M r *
      singleRayCorrectedReserve rho M r z c =
      singleRayContactDenom M r *
        (singleRayNatLocalGap rho M r +
          singleRayNatScalingReserve rho c r z) := by
    calc
      singleRayContactDenom M r *
          singleRayCorrectedReserve rho M r z c =
          singleRayEntropyResidual rho M r z c := hresidual.symm
      _ = singleRayContactDenom M r *
          (c * radialNatEntropy rho r z - lowerRayNatEnvelope rho M) :=
            hgap.symm
      _ = singleRayContactDenom M r *
          (singleRayNatLocalGap rho M r +
            singleRayNatScalingReserve rho c r z) := by rw [hdecomp]
  nlinarith

end CourtadeKumar
