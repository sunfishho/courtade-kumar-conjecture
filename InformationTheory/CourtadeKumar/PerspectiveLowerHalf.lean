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

/-- The affine-support part of the manuscript applies when the prescribed
mean ray has finite width parameter, equivalently `mean U < mean M`.  The
singular endpoint `mean U = mean M` is deliberately excluded here and is
handled by direct primal-dual equality below. -/
def OrderedTriangleLowerHalfStrictAffineSupportTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n M ≤ 1 / 2 →
    cubeAverage n U < cubeAverage n M →
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
          theta * E0 + a * cubeAverage n M + b * cubeAverage n U

/-- The direct Bellman assertion on the singular full-width face.  Its
proof in the manuscript uses primal-dual equality and does not require a
finite supporting slope in the radial variable. -/
def OrderedTriangleLowerHalfFullWidthBellmanStep (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n M ≤ 1 / 2 →
    cubeAverage n U = cubeAverage n M →
    cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) ≥
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2 →
    cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) ≥
      bellmanEnvelope (alpha : ℝ) (cubeAverage n M)

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

/-- This is the exact lower-half assembly used by the audited proof: finite
affine support off the singular ray, and direct primal equality on it. -/
theorem orderedTriangleLowerHalfBellmanStep_of_strictAffineSupport_and_fullWidth
    (alpha : ℝ≥0)
    (hsupport : OrderedTriangleLowerHalfStrictAffineSupportTheorem alpha)
    (hfull : OrderedTriangleLowerHalfFullWidthBellmanStep alpha) :
    OrderedTriangleLowerHalfBellmanStep alpha := by
  intro n M U hdomain hmean hentropy
  obtain hle := cubeAverage_mono (fun y ↦ (hdomain y).2.1)
  rcases hle.eq_or_lt with heq | hlt
  · exact hfull n M U hdomain hmean heq hentropy
  · let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    obtain ⟨theta, a, b, htheta, haffine, htarget⟩ :=
      hsupport n M U hdomain hmean hlt
    have hdual := orderedTriangle_weakDual_of_affineSupport
      hdomain htheta haffine (show E0 ≤
        cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) by
          simpa [E0] using hentropy)
    exact htarget.trans hdual

/-- Mixed strict-support/direct-endpoint certificates imply the complete
Courtade--Kumar statement without inventing an endpoint tangent. -/
theorem courtadeKumar_of_lowerHalfStrictAffineSupport_and_fullWidth
    (hsupport : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleLowerHalfStrictAffineSupportTheorem alpha)
    (hfull : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleLowerHalfFullWidthBellmanStep alpha) :
    Statement := by
  apply courtadeKumar_of_orderedEqualMultiplier
  intro alpha halpha
  exact orderedEqualMultiplier_of_orderedTriangle alpha
    (orderedTriangleBellmanStep_of_lowerHalf alpha
      (orderedTriangleLowerHalfBellmanStep_of_strictAffineSupport_and_fullWidth
        alpha (hsupport alpha halpha) (hfull alpha halpha)))

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
