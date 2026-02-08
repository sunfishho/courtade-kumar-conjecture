import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


open MeasureTheory

/-- A bundled random variable `X : Ω → α` on the canonical measure `volume`. -/
structure RandomVariable (Ω α : Type*)
    [MeasureSpace Ω] [MeasurableSpace α] [IsProbabilityMeasure (volume : Measure Ω)] where
  X : Ω → α
  measurable_X : Measurable X

namespace RandomVariable

variable {Ω α : Type*}
  [MeasureSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β]
  [IsProbabilityMeasure (volume : Measure Ω)]

/-- Give ProbabilityMeasure on Ω -/
noncomputable def μ (_ : RandomVariable Ω α) : ProbabilityMeasure Ω := by
  exact ⟨(volume : Measure Ω), by infer_instance⟩

/-- The pushforward (law) of `μ` by `X`. -/
noncomputable def law (rv : RandomVariable Ω α) : ProbabilityMeasure α :=
  ProbabilityMeasure.map rv.μ rv.measurable_X.aemeasurable

/-- Calculate joint random variable (X, Y) -/
noncomputable def joint_RV (X : RandomVariable Ω α) (Y : RandomVariable Ω β) :
  RandomVariable Ω (α × β) :=
  ⟨fun ω => (X.X ω, Y.X ω), X.measurable_X.prodMk Y.measurable_X⟩

-- Somehow the product measure is inferred to be the right joint measure,
-- which is correct in this instance
noncomputable def iid_joint_RVs {n : ℕ} (X : RandomVariable Ω α) :
    RandomVariable (Fin n → Ω) (Fin n → α) :=
    ⟨fun ω_vec i => X.X (ω_vec i),
    measurable_pi_lambda _ (fun i =>
    X.measurable_X.comp (measurable_pi_apply i)) ⟩

end RandomVariable
