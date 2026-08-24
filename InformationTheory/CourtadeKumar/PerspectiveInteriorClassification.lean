import InformationTheory.CourtadeKumar.BellmanEnvelopePositivity
import InformationTheory.CourtadeKumar.CanonicalPhaseSelection
import InformationTheory.CourtadeKumar.PerspectiveLowerHalf

/-! Interior lower-half perspective classification for cube averages. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Pointwise ordered-triangle feasibility passes to all three scalar mean
bounds used by the phase classification. -/
theorem orderedTriangle_cubeAverage_bounds
    {n : ℕ} {M U : BitVec n → ℝ}
    (hdomain : ∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) :
    0 ≤ cubeAverage n U ∧
      cubeAverage n U ≤ cubeAverage n M ∧
      cubeAverage n U ≤ 1 - cubeAverage n M ∧
      cubeAverage n M ∈ Icc (0 : ℝ) 1 := by
  have hMpoint : ∀ y, 0 ≤ M y ∧ M y ≤ 1 := by
    intro y
    exact ⟨(hdomain y).1.trans (hdomain y).2.1,
      by linarith [(hdomain y).1, (hdomain y).2.2]⟩
  have hU0 : 0 ≤ cubeAverage n U := by
    simpa using cubeAverage_mono
      (f := fun _ ↦ (0 : ℝ)) (g := U) (fun y ↦ (hdomain y).1)
  have hUM : cubeAverage n U ≤ cubeAverage n M :=
    cubeAverage_mono fun y ↦ (hdomain y).2.1
  have hUcomp : cubeAverage n U ≤ 1 - cubeAverage n M := by
    have h := cubeAverage_mono (f := U) (g := fun y ↦ 1 - M y)
      (fun y ↦ (hdomain y).2.2)
    simpa [cubeAverage_one_sub] using h
  exact ⟨hU0, hUM, hUcomp, cubeAverage_mem_Icc hMpoint⟩

/-- The direct entropy-root classification closes the genuine interior of
the lower-half cube-average problem. -/
theorem orderedTriangle_interiorLowerHalf_geometricTwoPhase
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (n : ℕ) (M U : BitVec n → ℝ)
    (hdomain : ∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y)
    (hmeanM : cubeAverage n M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hmeanU : 0 < cubeAverage n U)
    (hstrict : cubeAverage n U < cubeAverage n M) :
    let meanM := cubeAverage n M
    let meanU := cubeAverage n U
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (meanM - meanU) +
        bellmanEnvelope (alpha : ℝ) (meanM + meanU)) / 2
    Nonempty (SingleRayGeometryData alpha meanM meanU E0) ∨
      Nonempty (CenteredEndpointGeometryData alpha meanM meanU E0) := by
  dsimp
  obtain ⟨hU0, hUM, _, _⟩ := orderedTriangle_cubeAverage_bounds hdomain
  have hminus : cubeAverage n M - cubeAverage n U ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hUM]
    · linarith [hmeanM.2, hU0]
  have hplus : cubeAverage n M + cubeAverage n U ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · linarith [hmeanM.1, hU0]
    · linarith [hUM, hmeanM.2]
  have hE0 : 0 <
      (bellmanEnvelope (alpha : ℝ)
          (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ)
          (cubeAverage n M + cubeAverage n U)) / 2 :=
    centeredBellmanThreshold_pos halpha hminus hplus
  exact canonicalInteriorTwoPhaseGeometry halpha hmeanM hmeanU hstrict hE0 rfl

end CourtadeKumar
