import InformationTheory.CourtadeKumar.PerspectiveClosure
import InformationTheory.CourtadeKumar.OrderedTriangleSymmetry

/-! Correct lower-half interface for the perspective phase classification. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Affine certificates only in the complement-normalized regime
`cubeAverage M ≤ 1/2`, which is the actual domain of the perspective
classification. -/
def OrderedTriangleLowerHalfAffineSupportTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n M ≤ 1 / 2 →
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
          theta * E0 + a * cubeAverage n M + b * cubeAverage n U

theorem orderedTriangleLowerHalfBellmanStep_of_affineSupport
    (alpha : ℝ≥0)
    (hsupport : OrderedTriangleLowerHalfAffineSupportTheorem alpha) :
    OrderedTriangleLowerHalfBellmanStep alpha := by
  intro n M U hdomain hmean hentropy
  let E0 :=
    (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
      bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
  obtain ⟨theta, a, b, htheta, haffine, htarget⟩ :=
    hsupport n M U hdomain hmean
  have hdual := orderedTriangle_weakDual_of_affineSupport
    hdomain htheta haffine (show E0 ≤
      cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) by
        simpa [E0] using hentropy)
  exact htarget.trans hdual

theorem courtadeKumar_of_lowerHalfAffineSupport
    (hsupport : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleLowerHalfAffineSupportTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_orderedEqualMultiplier
  intro alpha halpha
  exact orderedEqualMultiplier_of_orderedTriangle alpha
    (orderedTriangleBellmanStep_of_lowerHalf alpha
      (orderedTriangleLowerHalfBellmanStep_of_affineSupport alpha
        (hsupport alpha halpha)))

/-- The two-phase contact classification in its exact lower-half domain. -/
def OrderedTriangleLowerHalfTwoPhaseTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n M ≤ 1 / 2 →
    let meanM := cubeAverage n M
    let meanU := cubeAverage n U
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (meanM - meanU) +
        bellmanEnvelope (alpha : ℝ) (meanM + meanU)) / 2
    Nonempty (SingleRayPhaseData alpha meanM meanU E0) ∨
      Nonempty (CenteredEndpointPhaseData alpha meanM meanU E0)

theorem lowerHalfAffineSupport_of_twoPhase
    (alpha : ℝ≥0)
    (hphase : OrderedTriangleLowerHalfTwoPhaseTheorem alpha) :
    OrderedTriangleLowerHalfAffineSupportTheorem alpha := by
  intro n M U hdomain hmean
  dsimp
  rcases hphase n M U hdomain hmean with hsingle | hcentered
  · rcases hsingle with ⟨hsingle⟩
    exact exists_affineSupport_of_singleRayPhase hsingle
  · rcases hcentered with ⟨hcentered⟩
    exact exists_affineSupport_of_centeredEndpointPhase hcentered

theorem courtadeKumar_of_lowerHalfTwoPhase
    (hphase : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleLowerHalfTwoPhaseTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_lowerHalfAffineSupport
  intro alpha halpha
  exact lowerHalfAffineSupport_of_twoPhase alpha (hphase alpha halpha)

end CourtadeKumar
