import InformationTheory.CourtadeKumar.PerspectiveFullWidth

/-! The two channel-parameter endpoints and the final LR-to-statement assembly.

The audited proof treats `alpha = 0` and `alpha = 1/2` directly.  Only the
open channel interval is delegated to the closed-ray LR theorem.
-/

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

/-- At crossover probability `1/2`, iid Bernoulli noise is uniform on the
Boolean cube. -/
theorem iidBernoulliPMF_half (n : ℕ) :
    iidBernoulliPMF n (1 / 2 : ℝ≥0) (by norm_num) = uniformInputPMF n := by
  ext z
  rw [iidBernoulliPMF_apply, uniformInputPMF_apply]
  simp_rw [PMF.bernoulli_apply]
  have hterm : ∀ x : Fin n,
      (bif z x then (1 / 2 : ℝ≥0) else 1 - (1 / 2 : ℝ≥0)) =
        (1 / 2 : ℝ≥0) := by
    intro x
    cases hzx : z x
    · apply NNReal.eq
      norm_num
    · rfl
  calc
    (∏ x, ↑(bif z x then (1 / 2 : ℝ≥0) else 1 - (1 / 2 : ℝ≥0))) =
        ∏ _x : Fin n, (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) := by
          apply Finset.prod_congr rfl
          intro x _
          rw [hterm x]
    _ = (2 ^ n : ℝ≥0∞)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hcoe : (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
        norm_num
      rw [hcoe]
      exact ENNReal.inv_pow.symm

/-- Pure noise makes the channel output uniform for every fixed input. -/
theorem bscOutputPMF_half (n : ℕ) (x : BitVec n) :
    bscOutputPMF n (1 / 2 : ℝ≥0) (by norm_num) x = uniformInputPMF n := by
  ext y
  rw [bscOutputPMF_apply, iidBernoulliPMF_half]
  simp

/-- Consequently the Boolean posterior is its prior, independently of the
observed channel output. -/
theorem bscPosteriorPMF_half (n : ℕ) (b : BitVec n → Bool) (y : BitVec n) :
    bscPosteriorPMF n (1 / 2 : ℝ≥0) (by norm_num) b y =
      (uniformInputPMF n).map b := by
  rw [bscPosteriorPMF, bscOutputPMF_half]

theorem bscPosteriorBias_half (n : ℕ) (b : BitVec n → Bool) (y : BitVec n) :
    bscPosteriorBias n (1 / 2 : ℝ≥0) (by norm_num) b y =
      bscPriorBias n b := by
  rw [bscPosteriorBias, bscPriorBias, bscPosteriorPMF_half]

theorem bscAveragePosteriorBinaryEntropy_half
    (n : ℕ) (b : BitVec n → Bool) :
    bscAveragePosteriorBinaryEntropy n (1 / 2 : ℝ≥0) (by norm_num) b =
      binaryEntropyBits (bscPriorBias n b) := by
  rw [bscAveragePosteriorBinaryEntropy_eq_cubeAverage]
  simp_rw [bscPosteriorBias_half]
  exact cubeAverage_const n _

/-- The output of a pure-noise BSC contains no information about the Boolean
function. -/
theorem bscMutualInformation_half (n : ℕ) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n (1 / 2 : ℝ≥0) (by norm_num) b).toMeasure = 0 := by
  rw [bscMutualInformation_eq_scalarEntropyDefect,
    bscAveragePosteriorBinaryEntropy_half, bscPriorBias]
  simp

theorem courtadeKumar_halfChannel
    (n : ℕ) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n (1 / 2 : ℝ≥0) (by norm_num) b).toMeasure
      ≤ ENNReal.ofReal (1 - binaryEntropyBits (1 / 2 : ℝ)) := by
  rw [bscMutualInformation_half]
  exact bot_le

/-- Standard reductions turn a lower-half ordered-triangle step into the
Boolean Bellman step used by the entropy induction. -/
theorem booleanBellmanStep_of_lowerHalf
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2)
    (hlower : OrderedTriangleLowerHalfBellmanStep alpha) :
    BooleanBellmanStep alpha :=
  booleanBellmanStep_of_orderedEqualMultiplier alpha
    (orderedEqualMultiplier_of_orderedTriangle alpha
      (orderedTriangleBellmanStep_of_lowerHalf alpha hlower))
    (bellmanEnvelopeSortingDominance alpha halpha)

/-- The noiseless channel endpoint follows from the manuscript's zero
Bellman envelope certificate. -/
theorem courtadeKumar_zeroChannel
    (n : ℕ) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n (0 : ℝ≥0) (by norm_num) b).toMeasure
      ≤ ENNReal.ofReal (1 - binaryEntropyBits (0 : ℝ)) := by
  exact bscMutualInformation_le_capacity_of_step 0 (by norm_num)
    (booleanBellmanStep_of_orderedEqualMultiplier 0
      (orderedEqualMultiplier_of_orderedTriangle 0
        (orderedTriangleBellmanStep_of_affineSupport 0
          orderedTriangleAffineSupportTheorem_zero))
      (bellmanEnvelopeSortingDominance 0 (by norm_num))) n b

/-- The complete theorem now has exactly the remaining hypothesis in the
audited proof: LR on each interior channel parameter and the full closed
shape interval.  The two channel endpoints are discharged directly above. -/
theorem courtadeKumar_of_closedScalarContact
    (hclosed : ∀ (alpha : ℝ≥0),
      (alpha : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) →
        SingleRayClosedScalarContactTheorem alpha) :
    Statement := by
  intro n alpha halpha b
  by_cases hzero : (alpha : ℝ) = 0
  · have halphaZero : alpha = 0 := by
      apply NNReal.eq
      exact hzero
    subst alpha
    exact courtadeKumar_zeroChannel n b
  by_cases hhalf : (alpha : ℝ) = 1 / 2
  · have halphaHalf : alpha = (1 / 2 : ℝ≥0) := by
      apply NNReal.eq
      norm_num at hhalf ⊢
      exact hhalf
    subst alpha
    exact courtadeKumar_halfChannel n b
  · have hinterior : (alpha : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := by
      constructor
      · exact lt_of_le_of_ne alpha.2 (Ne.symm hzero)
      · exact lt_of_le_of_ne halpha hhalf
    exact bscMutualInformation_le_capacity_of_step alpha halpha
      (booleanBellmanStep_of_lowerHalf alpha halpha
        (lowerHalfBellmanStep_of_closedScalarContact hinterior
          (hclosed alpha hinterior))) n b

end CourtadeKumar
