import InformationTheory.CourtadeKumar.SingleRayGainRatioReduction

/-! Closure of LR from the pure-entropy strict residual. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- The final strict scalar assertion after the Bellman coefficient and all
geometric auxiliary data have been eliminated. -/
def SingleRayEntropyResidualTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M r z : ℝ),
    M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    r ∈ Ioo (0 : ℝ) 1 →
    z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    M < z →
    M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 →
    0 ≤ singleRayEntropyResidual (channelRho (alpha : ℝ))
      M r z (M / z)

/-- The sharpened scalar bottleneck after separating the proved quadratic
entropy contraction from its nonnegative channel-curvature excess. -/
def SingleRayCorrectedReserveTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M r z : ℝ),
    M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    r ∈ Ioo (0 : ℝ) 1 →
    z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    M < z →
    M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 →
    0 ≤ singleRayCorrectedReserve (channelRho (alpha : ℝ))
      M r z (M / z)

/-- Normalized one-variable form of the strict reserve theorem. -/
def SingleRayGainRatioTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M r z : ℝ),
    M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    r ∈ Ioo (0 : ℝ) 1 →
    z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    M < z →
    M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 →
    singleRayGainRatioThreshold (channelRho (alpha : ℝ)) M r ≤
      radialNatChannelGainRatio (channelRho (alpha : ℝ)) r z

theorem singleRayCorrectedReserve_of_gainRatio
    (alpha : ℝ≥0) (hgain : SingleRayGainRatioTheorem alpha) :
    SingleRayCorrectedReserveTheorem alpha := by
  intro M r z hM hr hz hMz hcontact
  exact (singleRayCorrectedReserve_nonneg_iff_gainRatio
    hM.1 hz.1.ne').2 (hgain M r z hM hr hz hMz hcontact)

theorem singleRayEntropyResidual_of_correctedReserve
    (alpha : ℝ≥0) (hreserve : SingleRayCorrectedReserveTheorem alpha) :
    SingleRayEntropyResidualTheorem alpha := by
  intro M r z hM hr hz hMz hcontact
  have hcontactNat := singleRayNatContact_of_bitContact hz.1 hcontact
  exact singleRayEntropyResidual_nonneg_of_correctedReserve
    hM hr hcontactNat (hreserve M r z hM hr hz hMz hcontact)

theorem singleRayStrictReserve_of_entropyResidual
    (alpha : ℝ≥0) (hentropy : SingleRayEntropyResidualTheorem alpha) :
    SingleRayStrictReserveTheorem alpha := by
  intro M r z hM hr hz hMz hcontact
  have hcontactNat := singleRayNatContact_of_bitContact
    hz.1 hcontact
  have hresidual := hentropy M r z hM hr hz hMz hcontact
  have hgap := singleRayNatGap_nonneg_of_entropyResidual
    hM hr hcontactNat hresidual
  have hcz : M = M / z * z := by field_simp [hz.1.ne']
  have hdecomp := singleRayNatGap_eq_local_add_scalingReserve
    hcz hcontactNat
  have hgap' : 0 ≤
      M / z * radialNatEntropy (channelRho (alpha : ℝ)) r z -
        lowerRayNatEnvelope (channelRho (alpha : ℝ)) M :=
    sub_nonneg.mpr hgap
  rw [hdecomp] at hgap'
  exact hgap'

/-- The pure-entropy residual closes the complete single-ray LR interface. -/
theorem singleRayLR_of_entropyResidual
    (alpha : ℝ≥0) (hentropy : SingleRayEntropyResidualTheorem alpha) :
    SingleRayLRTheorem alpha :=
  singleRayLR_of_scalarContact alpha
    (singleRayScalarContact_of_strictReserve alpha
      (singleRayStrictReserve_of_entropyResidual alpha hentropy))

theorem orderedTriangleTwoPhase_of_geometry_and_entropyResidual
    (alpha : ℝ≥0)
    (hgeometry : OrderedTriangleGeometricTwoPhaseTheorem alpha)
    (hentropy : SingleRayEntropyResidualTheorem alpha) :
    OrderedTriangleTwoPhaseTheorem alpha :=
  orderedTriangleTwoPhase_of_geometry_and_LR alpha hgeometry
    (singleRayLR_of_entropyResidual alpha hentropy)

/-- End-to-end closure from perspective geometry and the pure-entropy
strict residual. -/
theorem courtadeKumar_of_perspectiveGeometry_and_entropyResidual
    (hgeometry : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleGeometricTwoPhaseTheorem alpha)
    (hentropy : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      SingleRayEntropyResidualTheorem alpha) :
    Statement :=
  courtadeKumar_of_perspectiveGeometry_and_LR hgeometry
    (fun alpha halpha ↦ singleRayLR_of_entropyResidual alpha
      (hentropy alpha halpha))

/-- End-to-end closure from perspective geometry and the corrected strict
reserve. -/
theorem courtadeKumar_of_perspectiveGeometry_and_correctedReserve
    (hgeometry : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleGeometricTwoPhaseTheorem alpha)
    (hreserve : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      SingleRayCorrectedReserveTheorem alpha) :
    Statement :=
  courtadeKumar_of_perspectiveGeometry_and_entropyResidual hgeometry
    (fun alpha halpha ↦ singleRayEntropyResidual_of_correctedReserve alpha
      (hreserve alpha halpha))

/-- End-to-end closure from perspective geometry and the normalized
gain-ratio inequality. -/
theorem courtadeKumar_of_perspectiveGeometry_and_gainRatio
    (hgeometry : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleGeometricTwoPhaseTheorem alpha)
    (hgain : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      SingleRayGainRatioTheorem alpha) :
    Statement :=
  courtadeKumar_of_perspectiveGeometry_and_correctedReserve hgeometry
    (fun alpha halpha ↦ singleRayCorrectedReserve_of_gainRatio alpha
      (hgain alpha halpha))

end CourtadeKumar
