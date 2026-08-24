import InformationTheory.CourtadeKumar.OrderedTriangle
import InformationTheory.CourtadeKumar.Statement

/-! Finite weak duality for the ordered-triangle Bellman problem.

This isolates the exact affine support certificate that the radial
perspective construction must produce.  No compactness, attainment, or
unproved scalar inequality is used in this module. -/

open scoped NNReal BigOperators

namespace CourtadeKumar

lemma cubeAverage_const_mul (n : ℕ) (a : ℝ) (f : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ a * f y) = a * cubeAverage n f := by
  unfold cubeAverage
  rw [← Finset.mul_sum]
  ring

/-- A global affine minorant for `j - theta e` on the ordered triangle. -/
def TriangleAffineSupport
    (alpha : ℝ≥0) (theta a b : ℝ) : Prop :=
  ∀ (m u : ℝ), 0 ≤ u → u ≤ m → u ≤ 1 - m →
    a * m + b * u ≤
      orderedTriangleChannelEntropy alpha m u -
        theta * orderedTriangleEntropy m u

/-- The exact certificate-producing assertion left to the perspective
geometry.  It allows the certificate to depend on the finite law and its
entropy threshold, exactly as the maximizing multiplier does. -/
def OrderedTriangleAffineSupportTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
          theta * E0 + a * cubeAverage n M + b * cubeAverage n U

/-- Averaging a global affine support gives the finite weak-duality bound. -/
theorem orderedTriangle_weakDual_of_affineSupport
    {alpha : ℝ≥0} {n : ℕ} {M U : BitVec n → ℝ}
    {E0 theta a b : ℝ}
    (hdomain : ∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y)
    (htheta : 0 ≤ theta)
    (hsupport : TriangleAffineSupport alpha theta a b)
    (hentropy : E0 ≤
      cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y))) :
    theta * E0 + a * cubeAverage n M + b * cubeAverage n U ≤
      cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) := by
  let e : BitVec n → ℝ := fun y ↦ orderedTriangleEntropy (M y) (U y)
  let j : BitVec n → ℝ := fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)
  have hpoint : ∀ y, theta * e y + (a * M y + b * U y) ≤ j y := by
    intro y
    have h := hsupport (M y) (U y) (hdomain y).1 (hdomain y).2.1 (hdomain y).2.2
    dsimp [e, j]
    linarith
  have havg := cubeAverage_mono hpoint
  have hlinear :
      cubeAverage n (fun y ↦ theta * e y + (a * M y + b * U y)) =
        theta * cubeAverage n e +
          (a * cubeAverage n M + b * cubeAverage n U) := by
    rw [cubeAverage_add, cubeAverage_const_mul, cubeAverage_add,
      cubeAverage_const_mul, cubeAverage_const_mul]
  rw [hlinear] at havg
  dsimp [j] at havg
  have hscaled := mul_le_mul_of_nonneg_left hentropy htheta
  dsimp [e] at hscaled havg
  linarith

/-- The perspective support theorem is sufficient for the complete ordered
triangle Bellman step. -/
theorem orderedTriangleBellmanStep_of_affineSupport
    (alpha : ℝ≥0)
    (hsupport : OrderedTriangleAffineSupportTheorem alpha) :
    OrderedTriangleBellmanStep alpha := by
  intro n M U hdomain hentropy
  let E0 :=
    (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
      bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
  obtain ⟨theta, a, b, htheta, haffine, htarget⟩ :=
    hsupport n M U hdomain
  have hdual := orderedTriangle_weakDual_of_affineSupport
    hdomain htheta haffine (show E0 ≤
      cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) by
        simpa [E0] using hentropy)
  exact htarget.trans hdual

/-- Consequently, affine support certificates at every admissible channel
imply the full Courtade--Kumar theorem. -/
theorem courtadeKumar_of_orderedTriangleAffineSupport
    (hsupport : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleAffineSupportTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_orderedEqualMultiplier
  intro alpha halpha
  exact orderedEqualMultiplier_of_orderedTriangle alpha
    (orderedTriangleBellmanStep_of_affineSupport alpha (hsupport alpha halpha))

end CourtadeKumar
