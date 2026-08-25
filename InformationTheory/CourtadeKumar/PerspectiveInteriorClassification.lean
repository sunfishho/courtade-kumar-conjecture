import InformationTheory.CourtadeKumar.BellmanEnvelopePositivity
import InformationTheory.CourtadeKumar.CanonicalPhaseSelection
import InformationTheory.CourtadeKumar.OrderedTriangleBoundary
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
    (hmeanM : cubeAverage n M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
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

/-- The manuscript's genuine interior perspective case already yields the
affine certificate consumed by weak duality once the single-ray scalar leaf
is supplied.  The centered leaf is discharged internally by corrected TOP. -/
theorem orderedTriangle_interiorLowerHalf_affineSupport
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hlr : SingleRayLRTheorem alpha)
    (n : ℕ) (M U : BitVec n → ℝ)
    (hdomain : ∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y)
    (hmeanM : cubeAverage n M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hmeanU : 0 < cubeAverage n U)
    (hstrict : cubeAverage n U < cubeAverage n M) :
    let E0 :=
      (bellmanEnvelope (alpha : ℝ)
          (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ)
          (cubeAverage n M + cubeAverage n U)) / 2
    ∃ theta a b : ℝ,
      0 ≤ theta ∧ TriangleAffineSupport alpha theta a b ∧
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
          theta * E0 + a * cubeAverage n M + b * cubeAverage n U := by
  dsimp
  rcases orderedTriangle_interiorLowerHalf_geometricTwoPhase
      halpha n M U hdomain hmeanM hmeanU hstrict with hsingle | hcentered
  · rcases hsingle with ⟨hsingle⟩
    exact exists_affineSupport_of_singleRayPhase
      (hsingle.toPhaseData hlr)
  · rcases hcentered with ⟨hcentered⟩
    exact exists_affineSupport_of_centeredEndpointPhase
      hcentered.toPhaseData

/-- The audited affine-support argument is now complete on its exact
nonsingular domain `mean U < mean M`.  The zero-width subcase has the
elementary multiplier `theta = 1`; every other case is genuine perspective
interior, including the midpoint face `mean M = 1/2`. -/
theorem lowerHalfStrictAffineSupport_of_interior_LR
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hlr : SingleRayLRTheorem alpha) :
    OrderedTriangleLowerHalfStrictAffineSupportTheorem alpha := by
  intro n M U hdomain hmean hstrict
  dsimp
  obtain ⟨hU0, _, _, _⟩ := orderedTriangle_cubeAverage_bounds hdomain
  by_cases hUzero : cubeAverage n U = 0
  · exact exists_orderedTriangleAffineSupport_of_averageU_eq_zero
      alpha halpha.2.le n M U hUzero
  · have hUpos : 0 < cubeAverage n U := lt_of_le_of_ne hU0 (Ne.symm hUzero)
    have hM : cubeAverage n M ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) :=
      ⟨hUpos.trans hstrict, hmean⟩
    exact orderedTriangle_interiorLowerHalf_affineSupport
      halpha hlr n M U hdomain hM hUpos hstrict

end CourtadeKumar
