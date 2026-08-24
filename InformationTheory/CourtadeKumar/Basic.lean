import InformationTheory.General.InformationQuantities
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory
open scoped ENNReal NNReal

namespace CourtadeKumar

/-- The discrete Boolean cube `{0,1}^n`, represented by Boolean-valued functions on `Fin n`. -/
abbrev BitVec (n : ℕ) := Fin n → Bool

/-- Coordinatewise addition modulo two. -/
def xorVec {n : ℕ} (x z : BitVec n) : BitVec n :=
  fun i ↦ Bool.xor (x i) (z i)

@[simp]
lemma xorVec_xorVec {n : ℕ} (x y : BitVec n) : xorVec x (xorVec x y) = y := by
  funext i
  change Bool.xor (x i) (Bool.xor (x i) (y i)) = y i
  cases x i <;> cases y i <;> rfl

lemma xorVec_left_bijective {n : ℕ} (x : BitVec n) : Function.Bijective (xorVec x) := by
  constructor
  · intro y z hyz
    have := congrArg (xorVec x) hyz
    simpa using this
  · intro y
    exact ⟨xorVec x y, xorVec_xorVec x y⟩

lemma xorVec_right_right {n : ℕ} (x z : BitVec n) :
    xorVec (xorVec x z) z = x := by
  funext i
  change Bool.xor (Bool.xor (x i) (z i)) (z i) = x i
  cases x i <;> cases z i <;> rfl

lemma xorVec_right_eq_iff {n : ℕ} (x y z : BitVec n) :
    xorVec x z = y ↔ x = xorVec y z := by
  constructor
  · intro h
    calc
      x = xorVec (xorVec x z) z := (xorVec_right_right x z).symm
      _ = xorVec y z := congrArg (fun w ↦ xorVec w z) h
  · rintro rfl
    exact xorVec_right_right y z

lemma map_xorVec_apply {n : ℕ} (q : PMF (BitVec n)) (x y : BitVec n) :
    q.map (xorVec x) y = q (xorVec x y) := by
  rw [PMF.map_apply, tsum_eq_single (xorVec x y)]
  · simp
  · intro z hz
    have hne : y ≠ xorVec x z := by
      intro h
      apply hz
      have hx := congrArg (xorVec x) h
      simpa using hx.symm
    simp [hne]

/-- A Bernoulli probability measure on one Boolean coordinate. -/
noncomputable def bernoulliProbabilityMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    ProbabilityMeasure Bool :=
  ⟨(PMF.bernoulli p hp).toMeasure, inferInstance⟩

/-- The law of `n` independent Bernoulli-`p` bits. -/
noncomputable def iidBernoulliPMF (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : PMF (BitVec n) :=
  (ProbabilityMeasure.pi fun _ : Fin n ↦ bernoulliProbabilityMeasure p hp).toMeasure.toPMF

lemma bernoulliProbabilityMeasure_singleton (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    (bernoulliProbabilityMeasure p hp).toMeasure {b} = PMF.bernoulli p hp b := by
  change (PMF.bernoulli p hp).toMeasure {b} = PMF.bernoulli p hp b
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]

lemma iidBernoulliPMF_apply (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (z : BitVec n) :
    iidBernoulliPMF n p hp z = ∏ i, PMF.bernoulli p hp (z i) := by
  rw [iidBernoulliPMF, Measure.toPMF_apply, ProbabilityMeasure.toMeasure_pi,
    Measure.pi_singleton]
  simp only [bernoulliProbabilityMeasure_singleton]

lemma iidBernoulliPMF_apply_eq_prod_cond (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (z : BitVec n) :
    iidBernoulliPMF n p hp z =
      ∏ i, cond (z i) (p : ℝ≥0∞) ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  rw [iidBernoulliPMF_apply]
  apply Finset.prod_congr rfl
  intro i _
  cases z i <;> simp [PMF.bernoulli_apply]

lemma iidBernoulliPMF_apply_xor (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (x y : BitVec n) :
    iidBernoulliPMF n p hp (xorVec x y) =
      ∏ i, if x i = y i then ((1 - p : ℝ≥0) : ℝ≥0∞) else (p : ℝ≥0∞) := by
  rw [iidBernoulliPMF_apply_eq_prod_cond]
  apply Finset.prod_congr rfl
  intro i _
  simp only [xorVec]
  cases x i <;> cases y i <;> simp [ENNReal.coe_sub]

lemma iidBernoulliPMF_map_eval (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (i : Fin n) :
    (iidBernoulliPMF n p hp).map (fun z ↦ z i) = PMF.bernoulli p hp := by
  apply PMF.toMeasure_inj.mp
  rw [← PMF.toMeasure_map (fun z ↦ z i) (iidBernoulliPMF n p hp)
    (measurable_pi_apply i)]
  rw [iidBernoulliPMF, Measure.toPMF_toMeasure]
  exact (measurePreserving_eval
    (μ := fun _ : Fin n ↦ (bernoulliProbabilityMeasure p hp).toMeasure) i).map_eq

/-- The uniform law on the Boolean cube. -/
noncomputable def uniformInputPMF (n : ℕ) : PMF (BitVec n) :=
  PMF.uniformOfFintype (BitVec n)

@[simp]
lemma card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  simp

@[simp]
lemma uniformInputPMF_apply (n : ℕ) (x : BitVec n) :
    uniformInputPMF n x = (2 ^ n : ℝ≥0∞)⁻¹ := by
  rw [uniformInputPMF, PMF.uniformOfFintype_apply, card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]

lemma uniformInputMeasure_singleton (n : ℕ) (x : BitVec n) :
    (uniformInputPMF n).toMeasure {x} = (2 ^ n : ℝ≥0∞)⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact uniformInputPMF_apply n x

lemma uniformInputPMF_map_xor_right (n : ℕ) (z : BitVec n) :
    (uniformInputPMF n).map (fun x ↦ xorVec x z) = uniformInputPMF n := by
  classical
  ext y
  rw [PMF.map_apply, tsum_eq_single (xorVec y z)]
  · rw [if_pos (xorVec_right_right y z).symm]
    simp
  · intro x hx
    rw [if_neg]
    intro h
    apply hx
    exact (xorVec_right_eq_iff x y z).mp h.symm

/-- Binary entropy in bits, built from Mathlib's natural-log binary entropy API. -/
noncomputable def binaryEntropyBits (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- The preceding definition agrees with the base-2 formula in the existing discrete library. -/
lemma binaryEntropyBits_eq_logb (p : ℝ) :
    binaryEntropyBits p =
      -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p) := by
  rw [binaryEntropyBits, Real.binEntropy]
  simp only [Real.log_inv, Real.logb]
  ring

lemma binaryEntropyBits_le_one (p : ℝ) : binaryEntropyBits p ≤ 1 := by
  rw [binaryEntropyBits, div_le_iff₀ (Real.log_pos (by norm_num))]
  simpa using (Real.binEntropy_le_log_two (p := p))

lemma bscCapacity_nonneg (p : ℝ) : 0 ≤ 1 - binaryEntropyBits p :=
  sub_nonneg.mpr (binaryEntropyBits_le_one p)

/-- The BSC output law conditional on a fixed input word. -/
noncomputable def bscOutputPMF (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (x : BitVec n) : PMF (BitVec n) :=
  (iidBernoulliPMF n alpha halpha).map (xorVec x)

@[simp]
lemma bscOutputPMF_apply (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (x y : BitVec n) :
    bscOutputPMF n alpha halpha x y = iidBernoulliPMF n alpha halpha (xorVec x y) := by
  exact map_xorVec_apply _ x y

lemma map_fixedBool_apply {n : ℕ} (q : PMF (BitVec n)) (c₀ c : Bool) (y : BitVec n) :
    q.map (fun y' ↦ (c₀, y')) (c, y) = if c = c₀ then q y else 0 := by
  rw [PMF.map_apply]
  by_cases h : c = c₀
  · subst c
    simp
  · simp [h]

/--
The joint law of `(b(X), Y)` in a binary symmetric channel:

* `X` is uniform on `{0,1}^n`;
* `Z` has independent Bernoulli-`alpha` coordinates and is independent of `X`;
* `Y = X xor Z`.

The nested `PMF.bind`/`PMF.map` construction makes the independence of `X` and `Z`
part of the definition rather than a separate hypothesis.
-/
noncomputable def bscJointPMF (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) : PMF (Bool × BitVec n) :=
  (uniformInputPMF n).bind fun x ↦
    (bscOutputPMF n alpha halpha x).map fun y ↦ (b x, y)

lemma bscJointPMF_apply (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (c : Bool) (y : BitVec n) :
    bscJointPMF n alpha halpha b (c, y) =
      ∑' x, uniformInputPMF n x *
        if c = b x then iidBernoulliPMF n alpha halpha (xorVec x y) else 0 := by
  rw [bscJointPMF, PMF.bind_apply]
  apply tsum_congr
  intro x
  rw [map_fixedBool_apply, bscOutputPMF_apply]

lemma bscJointPMF_apply_sum (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (c : Bool) (y : BitVec n) :
    bscJointPMF n alpha halpha b (c, y) =
      ∑ x : BitVec n, (2 ^ n : ℝ≥0∞)⁻¹ *
        if c = b x then iidBernoulliPMF n alpha halpha (xorVec x y) else 0 := by
  rw [bscJointPMF_apply, tsum_fintype]
  simp_rw [uniformInputPMF_apply]

lemma bscJointPMF_apply_explicit (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) (c : Bool) (y : BitVec n) :
    bscJointPMF n alpha halpha b (c, y) =
      (2 ^ n : ℝ≥0∞)⁻¹ * ∑ x : BitVec n,
        if c = b x then
          ∏ i, if x i = y i then ((1 - alpha : ℝ≥0) : ℝ≥0∞)
            else (alpha : ℝ≥0∞)
        else 0 := by
  rw [bscJointPMF_apply_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hbx : c = b x
  · simp only [hbx, if_true, iidBernoulliPMF_apply_xor]
  · simp only [hbx, if_false, mul_zero]

lemma bscJointPMF_map_fst (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    (bscJointPMF n alpha halpha b).map Prod.fst = (uniformInputPMF n).map b := by
  rw [bscJointPMF, PMF.map_bind]
  simp_rw [PMF.map_comp]
  simp_rw [bscOutputPMF]
  simp_rw [PMF.map_comp]
  change (uniformInputPMF n).bind (fun x ↦
      (iidBernoulliPMF n alpha halpha).map (fun _ ↦ b x)) =
    (uniformInputPMF n).map b
  have hmap :
      (fun x : BitVec n ↦
        (iidBernoulliPMF n alpha halpha).map (fun _ : BitVec n ↦ b x)) =
      (fun x ↦ PMF.pure (b x)) := by
    funext x
    change (iidBernoulliPMF n alpha halpha).map
        (Function.const (BitVec n) (b x)) = PMF.pure (b x)
    exact PMF.map_const (p := iidBernoulliPMF n alpha halpha) (b := b x)
  rw [hmap]
  rfl

lemma bscJointPMF_map_snd (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1)
    (b : BitVec n → Bool) :
    (bscJointPMF n alpha halpha b).map Prod.snd = uniformInputPMF n := by
  rw [bscJointPMF, PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (uniformInputPMF n).bind (fun x ↦
      (bscOutputPMF n alpha halpha x).map id) = uniformInputPMF n
  simp only [PMF.map_id]
  simp_rw [bscOutputPMF]
  change (uniformInputPMF n).bind (fun x ↦
      (iidBernoulliPMF n alpha halpha).bind (fun z ↦ PMF.pure (xorVec x z))) =
    uniformInputPMF n
  rw [PMF.bind_comm]
  change (iidBernoulliPMF n alpha halpha).bind (fun z ↦
      (uniformInputPMF n).map (fun x ↦ xorVec x z)) = uniformInputPMF n
  simp_rw [uniformInputPMF_map_xor_right]
  exact PMF.bind_const _ _

lemma crossover_le_one {alpha : ℝ≥0} (halpha : alpha ≤ 1 / 2) : alpha ≤ 1 :=
  halpha.trans (by norm_num)

end CourtadeKumar
