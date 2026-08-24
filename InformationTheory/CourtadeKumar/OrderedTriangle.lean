import InformationTheory.CourtadeKumar.EqualMultiplier

/-! Exact midpoint/half-width coordinates for the ordered Bellman step. -/

open scoped NNReal BigOperators

namespace CourtadeKumar

/-- Entropy of an ordered pair in midpoint/half-width coordinates. -/
noncomputable def orderedTriangleEntropy (m u : ℝ) : ℝ :=
  (binaryEntropyBits (m - u) + binaryEntropyBits (m + u)) / 2

/-- Entropy after the BSC contracts the half-width by `rho = 1-2 alpha`. -/
noncomputable def orderedTriangleChannelEntropy (alpha : ℝ≥0) (m u : ℝ) : ℝ :=
  (binaryEntropyBits (m - channelRho (alpha : ℝ) * u) +
      binaryEntropyBits (m + channelRho (alpha : ℝ) * u)) / 2

/-- The exact perspective-form scalar assertion on the ordered triangle. -/
def OrderedTriangleBellmanStep (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) ≥
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2 →
    cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) ≥
      bellmanEnvelope (alpha : ℝ) (cubeAverage n M)

lemma cubeAverage_midpoint (n : ℕ) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ (A y + B y) / 2) =
      (cubeAverage n A + cubeAverage n B) / 2 := by
  unfold cubeAverage
  simp only [div_eq_mul_inv, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

lemma cubeAverage_halfWidth (n : ℕ) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ (B y - A y) / 2) =
      (cubeAverage n B - cubeAverage n A) / 2 := by
  unfold cubeAverage
  simp only [div_eq_mul_inv, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

lemma orderedTriangleEntropy_midpoint_halfWidth (a b : ℝ) :
    orderedTriangleEntropy ((a + b) / 2) ((b - a) / 2) =
      (binaryEntropyBits a + binaryEntropyBits b) / 2 := by
  unfold orderedTriangleEntropy
  rw [show (a + b) / 2 - (b - a) / 2 = a by ring,
    show (a + b) / 2 + (b - a) / 2 = b by ring]

lemma orderedTriangleChannelEntropy_midpoint_halfWidth
    (alpha : ℝ≥0) (a b : ℝ) :
    orderedTriangleChannelEntropy alpha ((a + b) / 2) ((b - a) / 2) =
      binaryEntropyPair alpha a b := by
  unfold orderedTriangleChannelEntropy binaryEntropyPair channelRho
  rw [show (a + b) / 2 - (1 - 2 * (alpha : ℝ)) * ((b - a) / 2) =
      (1 - (alpha : ℝ)) * a + (alpha : ℝ) * b by ring,
    show (a + b) / 2 + (1 - 2 * (alpha : ℝ)) * ((b - a) / 2) =
      (alpha : ℝ) * a + (1 - (alpha : ℝ)) * b by ring]
  ring

lemma cubeAverage_orderedTriangleEntropy_midpoint_halfWidth
    (n : ℕ) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ orderedTriangleEntropy
        ((A y + B y) / 2) ((B y - A y) / 2)) =
      (cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
        cubeAverage n (fun y ↦ binaryEntropyBits (B y))) / 2 := by
  calc
    cubeAverage n (fun y ↦ orderedTriangleEntropy
        ((A y + B y) / 2) ((B y - A y) / 2)) =
        cubeAverage n (fun y ↦
          (binaryEntropyBits (A y) + binaryEntropyBits (B y)) / 2) := by
            apply cubeAverage_congr
            intro y
            exact orderedTriangleEntropy_midpoint_halfWidth (A y) (B y)
    _ = (cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
        cubeAverage n (fun y ↦ binaryEntropyBits (B y))) / 2 :=
      cubeAverage_midpoint n _ _

lemma cubeAverage_orderedTriangleChannelEntropy_midpoint_halfWidth
    (n : ℕ) (alpha : ℝ≥0) (A B : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha
        ((A y + B y) / 2) ((B y - A y) / 2)) =
      cubeAverage n (fun y ↦ binaryEntropyPair alpha (A y) (B y)) := by
  apply cubeAverage_congr
  intro y
  exact orderedTriangleChannelEntropy_midpoint_halfWidth alpha (A y) (B y)

/-- The triangle perspective assertion implies the ordered
equal-multiplier assertion required by the Boolean induction. -/
theorem orderedEqualMultiplier_of_orderedTriangle
    (alpha : ℝ≥0) (htriangle : OrderedTriangleBellmanStep alpha) :
    OrderedEqualMultiplierBellmanStep alpha := by
  intro n A B hA hB horder hentropy
  let M : BitVec n → ℝ := fun y ↦ (A y + B y) / 2
  let U : BitVec n → ℝ := fun y ↦ (B y - A y) / 2
  have hdomain : ∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y := by
    intro y
    dsimp [M, U]
    constructor
    · linarith [horder y]
    constructor
    · linarith [(hA y).1]
    · linarith [(hB y).2]
  have hM : cubeAverage n M =
      (cubeAverage n A + cubeAverage n B) / 2 := by
    simpa [M] using cubeAverage_midpoint n A B
  have hU : cubeAverage n U =
      (cubeAverage n B - cubeAverage n A) / 2 := by
    simpa [U] using cubeAverage_halfWidth n A B
  have hleft : cubeAverage n M - cubeAverage n U = cubeAverage n A := by
    rw [hM, hU]
    ring
  have hright : cubeAverage n M + cubeAverage n U = cubeAverage n B := by
    rw [hM, hU]
    ring
  have htriangleEntropy :
      cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) ≥
        (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
          bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2 := by
    rw [hleft, hright]
    have havg := cubeAverage_orderedTriangleEntropy_midpoint_halfWidth n A B
    rw [show cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) =
      (cubeAverage n (fun y ↦ binaryEntropyBits (A y)) +
        cubeAverage n (fun y ↦ binaryEntropyBits (B y))) / 2 by
          simpa [M, U] using havg]
    linarith
  have hresult := htriangle n M U hdomain htriangleEntropy
  rw [hM] at hresult
  have hchannel :=
    cubeAverage_orderedTriangleChannelEntropy_midpoint_halfWidth n alpha A B
  rw [show cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) =
    cubeAverage n (fun y ↦ binaryEntropyPair alpha (A y) (B y)) by
      simpa [M, U] using hchannel] at hresult
  exact hresult

end CourtadeKumar
