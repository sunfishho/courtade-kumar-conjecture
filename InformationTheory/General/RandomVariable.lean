import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.CondDistrib


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

-- The underlying measure on `Ω` is the canonical `volume`.
noncomputable def μ (_ : RandomVariable Ω α) : Measure Ω :=
  (volume : Measure Ω)

-- The pushforward (law) of `μ` by `X`.
noncomputable def law (rv : RandomVariable Ω α) : Measure α :=
  Measure.map rv.X (volume : Measure Ω)

-- -- Calculate joint random variable (X, Y)
noncomputable def joint_RV (X : RandomVariable Ω α) (Y : RandomVariable Ω β) :
RandomVariable Ω (α × β) := by
  exact (RandomVariable.mk (X := fun ω => (X.X ω, Y.X ω))
  (measurable_X := Measurable.prodMk X.measurable_X Y.measurable_X))

end RandomVariable
