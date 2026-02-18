import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.CondDistrib
import InformationTheory.General.RandomVariable


open MeasureTheory RandomVariable

/-- A bundled random variable `X : Ω → α` on the canonical measure `volume`. -/
structure DiscreteRandomVariable (Ω α : Type*)
    [MeasureSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α] [IsProbabilityMeasure (volume : Measure Ω)]
    [Countable α] [MeasurableSingletonClass α]
  extends RandomVariable Ω α


namespace DiscreteRandomVariable

variable {Ω α β : Type*}
  [MeasureSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α] [StandardBorelSpace α]
  [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [StandardBorelSpace β]
  [Countable β] [MeasurableSingletonClass β]
  [IsProbabilityMeasure (volume : Measure Ω)]

/-- Compute PMF -/
noncomputable def PMF (drv : DiscreteRandomVariable Ω α)
    [IsProbabilityMeasure (volume : Measure Ω)] : PMF α := by
  exact (RandomVariable.law (Ω := Ω) (α := α) drv.toRandomVariable).toMeasure.toPMF

-- Calculate P(Y|X)
noncomputable def conditional_PMF (X : DiscreteRandomVariable Ω α)
(Y : DiscreteRandomVariable Ω β) [Nonempty β] :
 ProbabilityTheory.Kernel α β := by
  haveI : IsFiniteMeasure (volume : Measure Ω) := by infer_instance
  exact ProbabilityTheory.condDistrib
    (μ := (volume : Measure Ω))
    (X := X.X)
    (Y := Y.X)

-- Calculate joint random variable (X, Y)
noncomputable def discrete_joint_RV (X : DiscreteRandomVariable Ω α)
(Y : DiscreteRandomVariable Ω β) :
DiscreteRandomVariable Ω (α × β) := by
  exact (DiscreteRandomVariable.mk (RandomVariable.mk (X := fun ω => (X.X ω, Y.X ω))
  (measurable_X := Measurable.prodMk X.measurable_X Y.measurable_X)))

/-- Calculate the likelihood of a realization of a sequence of iid random variable. -/
noncomputable def discrete_sequence_likelihood (X : DiscreteRandomVariable Ω α) {n : ℕ+}
(realization : Fin n → α) : ENNReal :=
  ∏ i, (X.PMF (realization i))

end DiscreteRandomVariable
