import InformationTheory.CourtadeKumar.CenteredPhaseTOP

/-! Reduction of the remaining perspective theorem to geometry and LR. -/

open scoped NNReal

namespace CourtadeKumar

/-- Single-ray phase geometry before the LR scalar objective bound is
inserted. -/
structure SingleRayGeometryData
    (alpha : ℝ≥0) (M d E0 : ℝ) where
  theta : ℝ
  c : ℝ → ℝ
  r : ℝ
  z : ℝ
  a : ℝ
  b : ℝ
  theta_nonneg : 0 ≤ theta
  z_pos : 0 < z
  contactProfile : RadialContactProfile alpha theta c
  affineMinorant : RadialAffineMinorant c a b
  affine_touches : a + b * r = c r
  radial_contact : c r = radialTriangleDifference alpha theta r z / z
  moment_contact : d = M * r
  entropy_contact : E0 = M / z * radialTriangleEntropy r z

/-- The precise scalar LR assertion needed after the perspective geometry
has selected its contact. -/
def SingleRayLRTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M d E0 : ℝ) (h : SingleRayGeometryData alpha M d E0),
    bellmanEnvelope (alpha : ℝ) M ≤
      M / h.z * radialTriangleChannelEntropy alpha h.r h.z

/-- LR upgrades single-ray geometry to complete phase data. -/
noncomputable def SingleRayGeometryData.toPhaseData
    {alpha : ℝ≥0} {M d E0 : ℝ}
    (hlr : SingleRayLRTheorem alpha)
    (h : SingleRayGeometryData alpha M d E0) :
    SingleRayPhaseData alpha M d E0 where
  theta := h.theta
  c := h.c
  r := h.r
  z := h.z
  a := h.a
  b := h.b
  theta_nonneg := h.theta_nonneg
  z_pos := h.z_pos
  contactProfile := h.contactProfile
  affineMinorant := h.affineMinorant
  affine_touches := h.affine_touches
  radial_contact := h.radial_contact
  moment_contact := h.moment_contact
  entropy_contact := h.entropy_contact
  lr_bound := hlr M d E0 h

/-- The two-phase output of the perspective/contact geometry, before the
already-isolated LR and TOP scalar estimates are inserted. -/
def OrderedTriangleGeometricTwoPhaseTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    let meanM := cubeAverage n M
    let meanU := cubeAverage n U
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (meanM - meanU) +
        bellmanEnvelope (alpha : ℝ) (meanM + meanU)) / 2
    Nonempty (SingleRayGeometryData alpha meanM meanU E0) ∨
      Nonempty (CenteredEndpointGeometryData alpha meanM meanU E0)

/-- Perspective geometry plus LR produce the complete two-phase theorem;
the centered branch is discharged internally by corrected TOP. -/
theorem orderedTriangleTwoPhase_of_geometry_and_LR
    (alpha : ℝ≥0)
    (hgeometry : OrderedTriangleGeometricTwoPhaseTheorem alpha)
    (hlr : SingleRayLRTheorem alpha) :
    OrderedTriangleTwoPhaseTheorem alpha := by
  intro n M U hdomain
  rcases hgeometry n M U hdomain with hsingle | hcentered
  · rcases hsingle with ⟨hsingle⟩
    exact Or.inl ⟨hsingle.toPhaseData hlr⟩
  · rcases hcentered with ⟨hcentered⟩
    exact Or.inr ⟨hcentered.toPhaseData⟩

/-- A direct end-to-end implication from the remaining geometric and LR
interfaces to Courtade--Kumar. -/
theorem courtadeKumar_of_perspectiveGeometry_and_LR
    (hgeometry : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleGeometricTwoPhaseTheorem alpha)
    (hlr : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      SingleRayLRTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_twoPhasePerspective
  intro alpha halpha
  exact orderedTriangleTwoPhase_of_geometry_and_LR alpha
    (hgeometry alpha halpha) (hlr alpha halpha)

end CourtadeKumar
