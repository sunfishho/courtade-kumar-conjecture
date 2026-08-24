import InformationTheory.CourtadeKumar.Entropy
import InformationTheory.CourtadeKumar.PosteriorRecursion

open scoped ENNReal NNReal BigOperators
open DiscreteInformationQuantities

namespace CourtadeKumar

/-- The real posterior probability that the Boolean output equals `true`. -/
noncomputable def bscPosteriorBias (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (y : BitVec n) : ℝ :=
  (bscPosteriorPMF n alpha halpha b y true).toReal

/-- The two binary-entropy contributions obtained after one final BSC observation. -/
noncomputable def posteriorEntropyPair (alpha : ℝ≥0) (A B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (binaryEntropyBits ((alpha : ℝ) * A + (1 - (alpha : ℝ)) * B)) +
    ENNReal.ofReal
      (binaryEntropyBits ((1 - (alpha : ℝ)) * A + (alpha : ℝ) * B))

/-- Exact `n + 1` conditional-entropy decomposition into the two last-bit sections. -/
lemma bscDiscreteConditionalEntropy_succ
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec (n + 1) → Bool) :
    discrete_conditional_entropy (bscJointPMF (n + 1) alpha halpha b) =
      (2 ^ (n + 1) : ℝ≥0∞)⁻¹ * ∑ y : BitVec n,
        posteriorEntropyPair alpha
          (bscPosteriorBias n alpha halpha (lastSection b false) y)
          (bscPosteriorBias n alpha halpha (lastSection b true) y) := by
  rw [bscDiscreteConditionalEntropy_eq_averageBinaryEntropy]
  apply congrArg (fun s : ℝ≥0∞ ↦ (2 ^ (n + 1) : ℝ≥0∞)⁻¹ * s)
  calc
    (∑ z : BitVec (n + 1),
        ENNReal.ofReal
          (binaryEntropyBits (bscPosteriorPMF (n + 1) alpha halpha b z true).toReal)) =
        ∑ yd : BitVec n × Bool,
          ENNReal.ofReal
            (binaryEntropyBits
              (bscPosteriorPMF (n + 1) alpha halpha b
                (bitVecSnoc yd.1 yd.2) true).toReal) := by
      apply Fintype.sum_equiv (bitVecSuccEquiv n)
      intro z
      have hz : bitVecSnoc (bitVecSuccEquiv n z).1 (bitVecSuccEquiv n z).2 = z :=
        (bitVecSuccEquiv n).symm_apply_apply z
      rw [hz]
    _ = ∑ y : BitVec n, ∑ d : Bool,
          ENNReal.ofReal
            (binaryEntropyBits
              (bscPosteriorPMF (n + 1) alpha halpha b
                (bitVecSnoc y d) true).toReal) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ y : BitVec n,
        posteriorEntropyPair alpha
          (bscPosteriorBias n alpha halpha (lastSection b false) y)
          (bscPosteriorBias n alpha halpha (lastSection b true) y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Fintype.sum_bool, posteriorEntropyPair]
      simp only [bscPosteriorBias]
      rw [bscPosterior_true_toReal_bitVecSnoc_true,
        bscPosterior_true_toReal_bitVecSnoc_false]

end CourtadeKumar
