import InformationTheory.CourtadeKumar.EntropyDefect
import InformationTheory.CourtadeKumar.EntropyRecursion

open scoped ENNReal NNReal BigOperators
open DiscreteInformationQuantities

namespace CourtadeKumar

lemma pmfEntropyNatReal_nonneg {γ : Type*} [Fintype γ] (p : PMF γ) :
    0 ≤ pmfEntropyNatReal p := by
  apply Finset.sum_nonneg
  intro x _
  apply Real.negMulLog_nonneg ENNReal.toReal_nonneg
  exact (ENNReal.toReal_le_toReal (p.apply_ne_top x) ENNReal.one_ne_top).2
    (p.coe_le_one x)

/-- Finite discrete entropy is the `ofReal` image of its ordinary-real entropy sum. -/
lemma discreteEntropy_eq_ofReal_pmfEntropyNatReal {γ : Type*} [Fintype γ]
    (p : PMF γ) :
    discrete_entropy p =
      ENNReal.ofReal (Real.logb 2 (Real.exp 1) * pmfEntropyNatReal p) := by
  have hcoeff : 0 ≤ Real.logb 2 (Real.exp 1) := by
    rw [Real.logb, Real.log_exp]
    positivity
  rw [discrete_entropy, tsum_fintype, pmfEntropyNatReal,
    ← ENNReal.ofReal_sum_of_nonneg]
  · rw [← ENNReal.ofReal_mul hcoeff]
  · intro x _
    apply Real.negMulLog_nonneg ENNReal.toReal_nonneg
    exact (ENNReal.toReal_le_toReal (p.apply_ne_top x) ENNReal.one_ne_top).2
      (p.coe_le_one x)

/-- The natural-log entropy sum of a Boolean PMF is Mathlib's binary entropy. -/
lemma pmfEntropyNatReal_bool (p : PMF Bool) :
    pmfEntropyNatReal p = Real.binEntropy (p true).toReal := by
  rw [pmfEntropyNatReal, Fintype.sum_bool,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    pmfBool_false_toReal]

/-- Scaling a Boolean natural-log entropy sum converts it to binary entropy in bits. -/
lemma logb_mul_pmfEntropyNatReal_bool (p : PMF Bool) :
    Real.logb 2 (Real.exp 1) * pmfEntropyNatReal p =
      binaryEntropyBits (p true).toReal := by
  rw [pmfEntropyNatReal_bool, binaryEntropyBits, Real.logb, Real.log_exp]
  ring

lemma sum_pmf_toReal {γ : Type*} [Fintype γ] (p : PMF γ) :
    ∑ x : γ, (p x).toReal = 1 := by
  have hsum : ∑ x : γ, p x = 1 := by
    simpa [tsum_fintype] using p.tsum_coe
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top x), ENNReal.toReal_one] at hreal
  exact hreal

/-- The real conditional-entropy sum of the BSC posterior family. -/
noncomputable def bscConditionalEntropyNatReal
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) : ℝ :=
  ∑ y : BitVec n, (uniformInputPMF n y).toReal *
    pmfEntropyNatReal (bscPosteriorPMF n alpha halpha b y)

/-- Natural-log entropy chain rule for the explicitly factorized BSC joint law. -/
lemma bscPmfEntropyNatReal_chain
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    pmfEntropyNatReal (bscJointPMF n alpha halpha b) =
      pmfEntropyNatReal (uniformInputPMF n) +
        bscConditionalEntropyNatReal n alpha halpha b := by
  simp only [pmfEntropyNatReal, bscConditionalEntropyNatReal]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ y : BitVec n, ∑ c : Bool,
        Real.negMulLog (bscJointPMF n alpha halpha b (c, y)).toReal) =
      ∑ y : BitVec n,
        (Real.negMulLog (uniformInputPMF n y).toReal +
          (uniformInputPMF n y).toReal *
            ∑ c : Bool,
              Real.negMulLog (bscPosteriorPMF n alpha halpha b y c).toReal) := by
        apply Finset.sum_congr rfl
        intro y _
        simp_rw [bscJointPMF_eq_output_mul_posterior, ENNReal.toReal_mul,
          Real.negMulLog_mul]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal,
          one_mul, ← Finset.mul_sum]
    _ = (∑ y : BitVec n, Real.negMulLog (uniformInputPMF n y).toReal) +
        ∑ y : BitVec n, (uniformInputPMF n y).toReal *
          ∑ c : Bool,
            Real.negMulLog (bscPosteriorPMF n alpha halpha b y c).toReal := by
      rw [Finset.sum_add_distrib]

/-- The posterior binary-entropy average appearing in the scalar Courtade--Kumar objective. -/
noncomputable def bscAveragePosteriorBinaryEntropy
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) : ℝ :=
  ∑ y : BitVec n, (uniformInputPMF n y).toReal *
    binaryEntropyBits (bscPosteriorPMF n alpha halpha b y true).toReal

lemma logb_mul_bscConditionalEntropyNatReal
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    Real.logb 2 (Real.exp 1) * bscConditionalEntropyNatReal n alpha halpha b =
      bscAveragePosteriorBinaryEntropy n alpha halpha b := by
  rw [bscConditionalEntropyNatReal, bscAveragePosteriorBinaryEntropy,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    Real.logb 2 (Real.exp 1) *
        ((uniformInputPMF n y).toReal *
          pmfEntropyNatReal (bscPosteriorPMF n alpha halpha b y)) =
      (uniformInputPMF n y).toReal *
        (Real.logb 2 (Real.exp 1) *
          pmfEntropyNatReal (bscPosteriorPMF n alpha halpha b y)) := by ring
    _ = (uniformInputPMF n y).toReal *
        binaryEntropyBits (bscPosteriorPMF n alpha halpha b y true).toReal := by
      rw [logb_mul_pmfEntropyNatReal_bool]

/-- Exact scalar entropy representation of the statement's measure-theoretic mutual information. -/
lemma bscMutualInformation_eq_scalarEntropyDefect
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha halpha b).toMeasure =
      ENNReal.ofReal
        (binaryEntropyBits (((uniformInputPMF n).map b) true).toReal -
          bscAveragePosteriorBinaryEntropy n alpha halpha b) := by
  rw [mutualInformation_toMeasure_eq_ofReal_pmfKLReal,
    pmfKLReal_independentMarginals,
    bscJointPMF_map_fst, bscJointPMF_map_snd,
    bscPmfEntropyNatReal_chain]
  apply congrArg ENNReal.ofReal
  calc
    Real.logb 2 (Real.exp 1) *
        (pmfEntropyNatReal ((uniformInputPMF n).map b) +
          pmfEntropyNatReal (uniformInputPMF n) -
          (pmfEntropyNatReal (uniformInputPMF n) +
            bscConditionalEntropyNatReal n alpha halpha b)) =
      Real.logb 2 (Real.exp 1) *
          pmfEntropyNatReal ((uniformInputPMF n).map b) -
        Real.logb 2 (Real.exp 1) *
          bscConditionalEntropyNatReal n alpha halpha b := by ring
    _ = binaryEntropyBits (((uniformInputPMF n).map b) true).toReal -
          bscAveragePosteriorBinaryEntropy n alpha halpha b := by
      rw [logb_mul_pmfEntropyNatReal_bool,
        logb_mul_bscConditionalEntropyNatReal]

end CourtadeKumar
