import InformationTheory.CourtadeKumar.RadialProfileSupport
import InformationTheory.CourtadeKumar.PerspectiveWeakDual

/-! Exact algebraic wiring of the single-ray and centered-endpoint phases. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Data produced by the perspective geometry in the single-ray phase. -/
structure SingleRayPhaseData
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
  lr_bound : bellmanEnvelope (alpha : ℝ) M ≤
    M / z * radialTriangleChannelEntropy alpha r z

/-- Data produced by the perspective geometry in the centered-endpoint
phase. -/
structure CenteredEndpointPhaseData
    (alpha : ℝ≥0) (M d E0 : ℝ) where
  theta : ℝ
  c : ℝ → ℝ
  rstar : ℝ
  theta_nonneg : 0 ≤ theta
  contactProfile : RadialContactProfile alpha theta c
  chordSupport : RadialChordSupport c rstar
  centered_contact : c rstar =
    2 * radialTriangleDifference alpha theta rstar (1 / 2)
  entropy_contact : E0 =
    2 * d / rstar * radialTriangleEntropy rstar (1 / 2)
  top_bound : bellmanEnvelope (alpha : ℝ) M ≤
    2 * d / rstar * radialTriangleChannelEntropy alpha rstar (1 / 2)

/-- In the single-ray phase, contact and the moment identities make the
affine dual value exactly the LR objective. -/
theorem exists_affineSupport_of_singleRayPhase
    {alpha : ℝ≥0} {M d E0 : ℝ}
    (h : SingleRayPhaseData alpha M d E0) :
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) M ≤ theta * E0 + a * M + b * d := by
  refine ⟨h.theta, h.a, h.b, h.theta_nonneg,
    triangleAffineSupport_of_radialMinorant h.contactProfile h.affineMinorant, ?_⟩
  have hz : h.z ≠ 0 := h.z_pos.ne'
  have hthetaE : h.theta * E0 =
      h.theta * (M / h.z * radialTriangleEntropy h.r h.z) :=
    congrArg (fun x : ℝ ↦ h.theta * x) h.entropy_contact
  have hbd : h.b * d = h.b * (M * h.r) :=
    congrArg (fun x : ℝ ↦ h.b * x) h.moment_contact
  have hdual :
      h.theta * E0 + h.a * M + h.b * d =
        M / h.z * radialTriangleChannelEntropy alpha h.r h.z := by
    calc
      h.theta * E0 + h.a * M + h.b * d =
          h.theta * (M / h.z * radialTriangleEntropy h.r h.z) +
            h.a * M + h.b * (M * h.r) := by linarith [hthetaE, hbd]
      _ = h.theta * (M / h.z * radialTriangleEntropy h.r h.z) +
          M * (h.a + h.b * h.r) := by ring
      _ = h.theta * (M / h.z * radialTriangleEntropy h.r h.z) +
          M * h.c h.r := by rw [h.affine_touches]
      _ = h.theta * (M / h.z * radialTriangleEntropy h.r h.z) +
          M * (radialTriangleDifference alpha h.theta h.r h.z / h.z) := by
            rw [h.radial_contact]
      _ = M / h.z * radialTriangleChannelEntropy alpha h.r h.z := by
        unfold radialTriangleDifference
        field_simp [hz]
        ring
  rw [hdual]
  exact h.lr_bound

/-- In the centered-endpoint phase, the chord slope and entropy contact make
the affine dual value exactly the TOP objective. -/
theorem exists_affineSupport_of_centeredEndpointPhase
    {alpha : ℝ≥0} {M d E0 : ℝ}
    (h : CenteredEndpointPhaseData alpha M d E0) :
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) M ≤ theta * E0 + a * M + b * d := by
  refine ⟨h.theta, 0, h.c h.rstar / h.rstar, h.theta_nonneg,
    triangleAffineSupport_of_radialChord h.contactProfile h.chordSupport, ?_⟩
  have hr : h.rstar ≠ 0 := h.chordSupport.1.ne'
  have hthetaE : h.theta * E0 =
      h.theta * (2 * d / h.rstar *
        radialTriangleEntropy h.rstar (1 / 2)) :=
    congrArg (fun x : ℝ ↦ h.theta * x) h.entropy_contact
  have hdual :
      h.theta * E0 + 0 * M + (h.c h.rstar / h.rstar) * d =
        2 * d / h.rstar *
          radialTriangleChannelEntropy alpha h.rstar (1 / 2) := by
    calc
      h.theta * E0 + 0 * M + (h.c h.rstar / h.rstar) * d =
          h.theta * (2 * d / h.rstar *
            radialTriangleEntropy h.rstar (1 / 2)) +
            (h.c h.rstar / h.rstar) * d := by linarith [hthetaE]
      _ = h.theta * (2 * d / h.rstar *
            radialTriangleEntropy h.rstar (1 / 2)) +
          (2 * radialTriangleDifference alpha h.theta h.rstar (1 / 2) /
            h.rstar) * d := by rw [h.centered_contact]
      _ = 2 * d / h.rstar *
          radialTriangleChannelEntropy alpha h.rstar (1 / 2) := by
        unfold radialTriangleDifference
        field_simp [hr]
        ring
  rw [hdual]
  exact h.top_bound

/-- The precise two-phase output required from the perspective/contact
classification for each finite law. -/
def OrderedTriangleTwoPhaseTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    let meanM := cubeAverage n M
    let meanU := cubeAverage n U
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (meanM - meanU) +
        bellmanEnvelope (alpha : ℝ) (meanM + meanU)) / 2
    Nonempty (SingleRayPhaseData alpha meanM meanU E0) ∨
      Nonempty (CenteredEndpointPhaseData alpha meanM meanU E0)

/-- The two-phase contact theorem, with LR and TOP bounds included in their
respective phase data, produces all affine certificates needed by weak
duality. -/
theorem orderedTriangleAffineSupport_of_twoPhase
    (alpha : ℝ≥0)
    (hphase : OrderedTriangleTwoPhaseTheorem alpha) :
    OrderedTriangleAffineSupportTheorem alpha := by
  intro n M U hdomain
  dsimp
  rcases hphase n M U hdomain with hsingle | hcentered
  · rcases hsingle with ⟨hsingle⟩
    exact exists_affineSupport_of_singleRayPhase hsingle
  · rcases hcentered with ⟨hcentered⟩
    exact exists_affineSupport_of_centeredEndpointPhase hcentered

/-- Thus the two-phase perspective theorem implies the full
Courtade--Kumar statement. -/
theorem courtadeKumar_of_twoPhasePerspective
    (hphase : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleTwoPhaseTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_orderedTriangleAffineSupport
  intro alpha halpha
  exact orderedTriangleAffineSupport_of_twoPhase alpha (hphase alpha halpha)

end CourtadeKumar
