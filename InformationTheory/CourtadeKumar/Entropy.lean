import InformationTheory.CourtadeKumar.Posterior
import InformationTheory.Discrete.DiscreteInformationQuantities

open scoped ENNReal NNReal
open DiscreteInformationQuantities

namespace CourtadeKumar

/-- For a Boolean PMF, the `false` mass is one minus the `true` mass. -/
lemma pmfBool_false_toReal (p : PMF Bool) :
    (p false).toReal = 1 - (p true).toReal := by
  have hsum : p true + p false = 1 := by
    simpa [tsum_fintype] using p.tsum_coe
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (p.apply_ne_top true) (p.apply_ne_top false),
    ENNReal.toReal_one] at hreal
  linarith

/-- Discrete entropy of a Boolean PMF is binary entropy of its `true` atom. -/
lemma discreteEntropy_bool (p : PMF Bool) :
    discrete_entropy p = ENNReal.ofReal (binaryEntropyBits (p true).toReal) := by
  let q : ℝ := (p true).toReal
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 :=
    (ENNReal.toReal_le_toReal (p.apply_ne_top true) ENNReal.one_ne_top).2
      (p.coe_le_one true)
  have hnq : 0 ≤ Real.negMulLog q := Real.negMulLog_nonneg hq0 hq1
  have hnq' : 0 ≤ Real.negMulLog (1 - q) :=
    Real.negMulLog_nonneg (by linarith) (by linarith)
  have hcoeff : Real.logb 2 (Real.exp 1) = (Real.log 2)⁻¹ := by
    rw [Real.logb, Real.log_exp]
    simp
  have hcoeff0 : 0 ≤ Real.logb 2 (Real.exp 1) := by
    rw [hcoeff]
    positivity
  rw [discrete_entropy, tsum_fintype, Fintype.sum_bool, pmfBool_false_toReal]
  change ENNReal.ofReal (Real.logb 2 (Real.exp 1)) *
      (ENNReal.ofReal (Real.negMulLog q) + ENNReal.ofReal (Real.negMulLog (1 - q))) = _
  rw [← ENNReal.ofReal_add hnq hnq', ← ENNReal.ofReal_mul hcoeff0]
  apply congrArg ENNReal.ofReal
  rw [binaryEntropyBits, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hcoeff]
  ring

/-- Conditional entropy is the output-weighted average of the posterior entropies. -/
lemma bscDiscreteConditionalEntropy_eq_weightedPosteriorEntropy
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    discrete_conditional_entropy (bscJointPMF n alpha halpha b) =
      ∑ y : BitVec n, uniformInputPMF n y *
        discrete_entropy (bscPosteriorPMF n alpha halpha b y) := by
  rw [discrete_conditional_entropy]
  dsimp only
  rw [bscJointPMF_map_snd]
  simp_rw [if_neg (uniformInputPMF_ne_zero n _)]
  simp_rw [← bscPosteriorPMF_eq_joint_div_output]
  rw [tsum_fintype]
  simp_rw [discrete_entropy]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ac_rfl

/-- Conditional entropy is the uniform average of binary entropies of the posterior bias. -/
lemma bscDiscreteConditionalEntropy_eq_averageBinaryEntropy
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    discrete_conditional_entropy (bscJointPMF n alpha halpha b) =
      (2 ^ n : ℝ≥0∞)⁻¹ * ∑ y : BitVec n,
        ENNReal.ofReal
          (binaryEntropyBits (bscPosteriorPMF n alpha halpha b y true).toReal) := by
  rw [bscDiscreteConditionalEntropy_eq_weightedPosteriorEntropy]
  simp_rw [discreteEntropy_bool, uniformInputPMF_apply]
  rw [Finset.mul_sum]

end CourtadeKumar
