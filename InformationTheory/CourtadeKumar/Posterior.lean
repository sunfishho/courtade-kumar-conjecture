import InformationTheory.CourtadeKumar.Basic

open scoped ENNReal NNReal

namespace CourtadeKumar

/--
The posterior law of `b(X)` after observing the BSC output `Y = y`.

For a uniform input, channel symmetry says that `X | (Y = y)` has the same
law as `y xor Z`, where `Z` is the original iid Bernoulli noise.  Encoding the
posterior as a `PMF` makes its normalization part of the definition.
-/
noncomputable def bscPosteriorPMF (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (y : BitVec n) : PMF Bool :=
  (bscOutputPMF n alpha halpha y).map b

/-- The posterior atom formula, written as a finite sum over possible inputs. -/
lemma bscPosteriorPMF_apply (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (y : BitVec n) (c : Bool) :
    bscPosteriorPMF n alpha halpha b y c =
      ∑ x : BitVec n,
        if c = b x then iidBernoulliPMF n alpha halpha (xorVec x y) else 0 := by
  rw [bscPosteriorPMF, PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [bscOutputPMF_apply, xorVec_comm y x]
  by_cases h : c = b x <;> simp [h]

/--
Exact Bayes factorization.  Since the output marginal is uniform, the joint
atom is the output atom times the posterior atom.
-/
lemma bscJointPMF_eq_output_mul_posterior (n : ℕ) (alpha : ℝ≥0)
    (halpha : alpha ≤ 1) (b : BitVec n → Bool) (c : Bool) (y : BitVec n) :
    bscJointPMF n alpha halpha b (c, y) =
      uniformInputPMF n y * bscPosteriorPMF n alpha halpha b y c := by
  rw [bscJointPMF_apply_sum, uniformInputPMF_apply, bscPosteriorPMF_apply,
    Finset.mul_sum]

@[simp]
lemma uniformInputPMF_ne_zero (n : ℕ) (y : BitVec n) : uniformInputPMF n y ≠ 0 := by
  rw [uniformInputPMF_apply]
  simp

@[simp]
lemma uniformInputPMF_ne_top (n : ℕ) (y : BitVec n) : uniformInputPMF n y ≠ ∞ := by
  rw [uniformInputPMF_apply]
  simp

/-- The PMF above is literally the joint atom divided by the output atom. -/
lemma bscPosteriorPMF_eq_joint_div_output (n : ℕ) (alpha : ℝ≥0)
    (halpha : alpha ≤ 1) (b : BitVec n → Bool) (y : BitVec n) (c : Bool) :
    bscPosteriorPMF n alpha halpha b y c =
      bscJointPMF n alpha halpha b (c, y) / uniformInputPMF n y := by
  rw [bscJointPMF_eq_output_mul_posterior]
  rw [mul_comm (uniformInputPMF n y)]
  exact (ENNReal.mul_div_cancel_right (uniformInputPMF_ne_zero n y)
    (uniformInputPMF_ne_top n y)).symm

/-- Every posterior atom is a genuine probability in `[0,1]`. -/
lemma bscPosteriorPMF_apply_le_one (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (y : BitVec n) (c : Bool) :
    bscPosteriorPMF n alpha halpha b y c ≤ 1 :=
  PMF.coe_le_one _ _

/-- The two Boolean posterior atoms add to one. -/
lemma bscPosteriorPMF_false_add_true (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (y : BitVec n) :
    bscPosteriorPMF n alpha halpha b y false +
        bscPosteriorPMF n alpha halpha b y true = 1 := by
  simpa [tsum_fintype, add_comm] using (bscPosteriorPMF n alpha halpha b y).tsum_coe

end CourtadeKumar
