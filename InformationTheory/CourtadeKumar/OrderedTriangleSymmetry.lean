import InformationTheory.CourtadeKumar.PerspectiveWeakDual

/-! Complement symmetry reduction for the ordered-triangle problem. -/

open scoped NNReal BigOperators

namespace CourtadeKumar

@[simp] lemma binaryEntropyBits_one_sub (p : ℝ) :
    binaryEntropyBits (1 - p) = binaryEntropyBits p := by
  unfold binaryEntropyBits
  rw [Real.binEntropy_one_sub]

@[simp] lemma bellmanEnvelope_one_sub (alpha p : ℝ) :
    bellmanEnvelope alpha (1 - p) = bellmanEnvelope alpha p := by
  unfold bellmanEnvelope
  rw [binaryEntropyBits_one_sub]
  ring

@[simp] lemma orderedTriangleEntropy_complement (m u : ℝ) :
    orderedTriangleEntropy (1 - m) u = orderedTriangleEntropy m u := by
  unfold orderedTriangleEntropy
  rw [show 1 - m - u = 1 - (m + u) by ring,
    show 1 - m + u = 1 - (m - u) by ring,
    binaryEntropyBits_one_sub, binaryEntropyBits_one_sub]
  ring

@[simp] lemma orderedTriangleChannelEntropy_complement
    (alpha : ℝ≥0) (m u : ℝ) :
    orderedTriangleChannelEntropy alpha (1 - m) u =
      orderedTriangleChannelEntropy alpha m u := by
  unfold orderedTriangleChannelEntropy
  rw [show 1 - m - channelRho (alpha : ℝ) * u =
      1 - (m + channelRho (alpha : ℝ) * u) by ring,
    show 1 - m + channelRho (alpha : ℝ) * u =
      1 - (m - channelRho (alpha : ℝ) * u) by ring,
    binaryEntropyBits_one_sub, binaryEntropyBits_one_sub]
  ring

lemma cubeAverage_one_sub (n : ℕ) (M : BitVec n → ℝ) :
    cubeAverage n (fun y ↦ 1 - M y) = 1 - cubeAverage n M := by
  calc
    cubeAverage n (fun y ↦ 1 - M y) =
        cubeAverage n (fun y ↦ (1 : ℝ) + (-1) * M y) := by
          apply cubeAverage_congr
          intro y
          ring
    _ = cubeAverage n (fun _ ↦ (1 : ℝ)) +
        cubeAverage n (fun y ↦ (-1 : ℝ) * M y) := cubeAverage_add n _ _
    _ = 1 - cubeAverage n M := by
      rw [cubeAverage_const, cubeAverage_const_mul]
      ring

/-- The lower-half version of the ordered-triangle assertion used by the
perspective theorem. -/
def OrderedTriangleLowerHalfBellmanStep (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n M ≤ 1 / 2 →
    cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) ≥
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2 →
    cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) ≥
      bellmanEnvelope (alpha : ℝ) (cubeAverage n M)

/-- Complement symmetry shows that proving the perspective theorem for
mean midpoint at most one half loses no cases. -/
theorem orderedTriangleBellmanStep_of_lowerHalf
    (alpha : ℝ≥0)
    (hlower : OrderedTriangleLowerHalfBellmanStep alpha) :
    OrderedTriangleBellmanStep alpha := by
  intro n M U hdomain hentropy
  by_cases hM : cubeAverage n M ≤ 1 / 2
  · exact hlower n M U hdomain hM hentropy
  · let Mc : BitVec n → ℝ := fun y ↦ 1 - M y
    have hdomainc : ∀ y, 0 ≤ U y ∧ U y ≤ Mc y ∧ U y ≤ 1 - Mc y := by
      intro y
      dsimp [Mc]
      exact ⟨(hdomain y).1, (hdomain y).2.2,
        by simpa only [sub_sub_cancel] using (hdomain y).2.1⟩
    have hMc : cubeAverage n Mc = 1 - cubeAverage n M := by
      simpa [Mc] using cubeAverage_one_sub n M
    have hMclower : cubeAverage n Mc ≤ 1 / 2 := by
      rw [hMc]
      linarith
    have hleft : cubeAverage n Mc - cubeAverage n U =
        1 - (cubeAverage n M + cubeAverage n U) := by rw [hMc]; ring
    have hright : cubeAverage n Mc + cubeAverage n U =
        1 - (cubeAverage n M - cubeAverage n U) := by rw [hMc]; ring
    have hentropyc :
        cubeAverage n (fun y ↦ orderedTriangleEntropy (Mc y) (U y)) ≥
          (bellmanEnvelope (alpha : ℝ)
              (cubeAverage n Mc - cubeAverage n U) +
            bellmanEnvelope (alpha : ℝ)
              (cubeAverage n Mc + cubeAverage n U)) / 2 := by
      rw [hleft, hright, bellmanEnvelope_one_sub, bellmanEnvelope_one_sub]
      have heq : cubeAverage n (fun y ↦ orderedTriangleEntropy (Mc y) (U y)) =
          cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)) := by
        apply cubeAverage_congr
        intro y
        simp [Mc]
      rw [heq]
      linarith
    have hresult := hlower n Mc U hdomainc hMclower hentropyc
    rw [hMc, bellmanEnvelope_one_sub] at hresult
    have heq :
        cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (Mc y) (U y)) =
          cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) := by
      apply cubeAverage_congr
      intro y
      simp [Mc]
    rwa [heq] at hresult

end CourtadeKumar
