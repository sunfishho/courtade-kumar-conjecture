import InformationTheory.CourtadeKumar.CubeSplit
import InformationTheory.CourtadeKumar.Posterior

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

/-- Append one Boolean coordinate at the end of a cube point. -/
def bitVecSnoc {n : ℕ} (x : BitVec n) (d : Bool) : BitVec (n + 1) :=
  (bitVecSuccEquiv n).symm (x, d)

@[simp]
lemma bitVecSnoc_castSucc {n : ℕ} (x : BitVec n) (d : Bool) (i : Fin n) :
    bitVecSnoc x d i.castSucc = x i := by
  simp [bitVecSnoc]

@[simp]
lemma bitVecSnoc_last {n : ℕ} (x : BitVec n) (d : Bool) :
    bitVecSnoc x d (Fin.last n) = d := by
  simp [bitVecSnoc]

/-- The section of a Boolean function obtained by fixing its last input bit. -/
def lastSection {n : ℕ} (b : BitVec (n + 1) → Bool) (d : Bool) :
    BitVec n → Bool :=
  fun x ↦ b (bitVecSnoc x d)

@[simp]
lemma xorVec_bitVecSnoc {n : ℕ} (x y : BitVec n) (d e : Bool) :
    xorVec (bitVecSnoc x d) (bitVecSnoc y e) =
      bitVecSnoc (xorVec x y) (Bool.xor d e) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [xorVec]
  · simp [xorVec]

/-- The iid noise atom factors into its first `n` coordinates and its last coordinate. -/
lemma iidBernoulliPMF_apply_bitVecSnoc (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (z : BitVec n) (e : Bool) :
    iidBernoulliPMF (n + 1) alpha halpha (bitVecSnoc z e) =
      iidBernoulliPMF n alpha halpha z * PMF.bernoulli alpha halpha e := by
  rw [iidBernoulliPMF_apply, iidBernoulliPMF_apply, Fin.prod_univ_castSucc]
  simp [bitVecSnoc]

/-- Posterior recursion before specializing the observed last output bit. -/
lemma bscPosteriorPMF_apply_bitVecSnoc (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec (n + 1) → Bool) (y : BitVec n) (d c : Bool) :
    bscPosteriorPMF (n + 1) alpha halpha b (bitVecSnoc y d) c =
      ∑ e : Bool, PMF.bernoulli alpha halpha (Bool.xor e d) *
        bscPosteriorPMF n alpha halpha (lastSection b e) y c := by
  rw [bscPosteriorPMF_apply]
  calc
    (∑ x : BitVec (n + 1),
        if c = b x then
          iidBernoulliPMF (n + 1) alpha halpha (xorVec x (bitVecSnoc y d))
        else 0) =
        ∑ z : BitVec n × Bool,
          if c = b (bitVecSnoc z.1 z.2) then
            iidBernoulliPMF (n + 1) alpha halpha
              (xorVec (bitVecSnoc z.1 z.2) (bitVecSnoc y d))
          else 0 := by
      apply Fintype.sum_equiv (bitVecSuccEquiv n)
      intro x
      have hx : bitVecSnoc (bitVecSuccEquiv n x).1 (bitVecSuccEquiv n x).2 = x := by
        exact (bitVecSuccEquiv n).symm_apply_apply x
      rw [hx]
    _ = ∑ x : BitVec n, ∑ e : Bool,
          if c = b (bitVecSnoc x e) then
            iidBernoulliPMF n alpha halpha (xorVec x y) *
              PMF.bernoulli alpha halpha (Bool.xor e d)
          else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro e _
      rw [xorVec_bitVecSnoc, iidBernoulliPMF_apply_bitVecSnoc]
    _ = ∑ e : Bool, PMF.bernoulli alpha halpha (Bool.xor e d) *
          bscPosteriorPMF n alpha halpha (lastSection b e) y c := by
      simp_rw [bscPosteriorPMF_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : c = b (bitVecSnoc x e)
      · simp [lastSection, h, mul_comm]
      · simp [lastSection, h]

/-- Bayes recursion when the observed last output bit is `false`. -/
lemma bscPosteriorPMF_apply_bitVecSnoc_false (n : ℕ) (alpha : ℝ≥0)
    (halpha : alpha ≤ 1) (b : BitVec (n + 1) → Bool) (y : BitVec n) (c : Bool) :
    bscPosteriorPMF (n + 1) alpha halpha b (bitVecSnoc y false) c =
      ((1 - alpha : ℝ≥0) : ℝ≥0∞) *
          bscPosteriorPMF n alpha halpha (lastSection b false) y c +
        (alpha : ℝ≥0∞) *
          bscPosteriorPMF n alpha halpha (lastSection b true) y c := by
  rw [bscPosteriorPMF_apply_bitVecSnoc, Fintype.sum_bool]
  simp [PMF.bernoulli_apply, add_comm]

/-- Bayes recursion when the observed last output bit is `true`. -/
lemma bscPosteriorPMF_apply_bitVecSnoc_true (n : ℕ) (alpha : ℝ≥0)
    (halpha : alpha ≤ 1) (b : BitVec (n + 1) → Bool) (y : BitVec n) (c : Bool) :
    bscPosteriorPMF (n + 1) alpha halpha b (bitVecSnoc y true) c =
      (alpha : ℝ≥0∞) *
          bscPosteriorPMF n alpha halpha (lastSection b false) y c +
        ((1 - alpha : ℝ≥0) : ℝ≥0∞) *
          bscPosteriorPMF n alpha halpha (lastSection b true) y c := by
  rw [bscPosteriorPMF_apply_bitVecSnoc, Fintype.sum_bool]
  simp [PMF.bernoulli_apply, add_comm]

/-- The `true` posterior bias for final output `false`, as an affine real mixture. -/
lemma bscPosterior_true_toReal_bitVecSnoc_false
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec (n + 1) → Bool) (y : BitVec n) :
    (bscPosteriorPMF (n + 1) alpha halpha b (bitVecSnoc y false) true).toReal =
      (1 - (alpha : ℝ)) *
          (bscPosteriorPMF n alpha halpha (lastSection b false) y true).toReal +
        (alpha : ℝ) *
          (bscPosteriorPMF n alpha halpha (lastSection b true) y true).toReal := by
  rw [bscPosteriorPMF_apply_bitVecSnoc_false]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (by simp)
      ((bscPosteriorPMF n alpha halpha (lastSection b false) y).apply_ne_top true))
    (ENNReal.mul_ne_top (by simp)
      ((bscPosteriorPMF n alpha halpha (lastSection b true) y).apply_ne_top true)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal,
    NNReal.coe_sub halpha]
  norm_num

/-- The `true` posterior bias for final output `true`, as an affine real mixture. -/
lemma bscPosterior_true_toReal_bitVecSnoc_true
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec (n + 1) → Bool) (y : BitVec n) :
    (bscPosteriorPMF (n + 1) alpha halpha b (bitVecSnoc y true) true).toReal =
      (alpha : ℝ) *
          (bscPosteriorPMF n alpha halpha (lastSection b false) y true).toReal +
        (1 - (alpha : ℝ)) *
          (bscPosteriorPMF n alpha halpha (lastSection b true) y true).toReal := by
  rw [bscPosteriorPMF_apply_bitVecSnoc_true]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (by simp)
      ((bscPosteriorPMF n alpha halpha (lastSection b false) y).apply_ne_top true))
    (ENNReal.mul_ne_top (by simp)
      ((bscPosteriorPMF n alpha halpha (lastSection b true) y).apply_ne_top true)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal,
    NNReal.coe_sub halpha]
  norm_num

end CourtadeKumar
