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

/-- A Bernoulli probability measure on one Boolean coordinate. -/
noncomputable def bernoulliProbabilityMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    ProbabilityMeasure Bool :=
  ⟨(PMF.bernoulli p hp).toMeasure, inferInstance⟩

/-- The law of `n` independent Bernoulli-`p` bits. -/
noncomputable def iidBernoulliPMF (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : PMF (BitVec n) :=
  (ProbabilityMeasure.pi fun _ : Fin n ↦ bernoulliProbabilityMeasure p hp).toMeasure.toPMF

/-- The uniform law on the Boolean cube. -/
noncomputable def uniformInputPMF (n : ℕ) : PMF (BitVec n) :=
  PMF.uniformOfFintype (BitVec n)

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
    (iidBernoulliPMF n alpha halpha).map fun z ↦ (b x, xorVec x z)

lemma crossover_le_one {alpha : ℝ≥0} (halpha : alpha ≤ 1 / 2) : alpha ≤ 1 :=
  halpha.trans (by norm_num)

end CourtadeKumar
