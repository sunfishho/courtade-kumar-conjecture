import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.CondDistrib


open MeasureTheory

/-- A bundled random variable `X : Ω → α` on the canonical measure `volume`. -/
structure DiscreteRV (Ω α : Type*)
    [MeasureSpace Ω] [MeasurableSpace α] [IsProbabilityMeasure (volume : Measure Ω)]
    [Countable α] [MeasurableSingletonClass α] where
  X : Ω → α
  measurable_X : Measurable X

namespace DiscreteRV

variable {Ω α : Type*}
  [MeasureSpace Ω] [MeasurableSpace α]
  [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β]
  [Countable β] [MeasurableSingletonClass β]
  [IsProbabilityMeasure (volume : Measure Ω)]

-- The underlying measure on `Ω` is the canonical `volume`.
noncomputable def μ (_ : DiscreteRV Ω α) : Measure Ω :=
  (volume : Measure Ω)

-- The pushforward (law) of `μ` by `X`.
noncomputable def law (rv : DiscreteRV Ω α) : Measure α :=
  Measure.map rv.X (volume : Measure Ω)

-- The law as a `PMF α`. Requires that `volume` is a probability measure.
noncomputable def PMF (rv : DiscreteRV Ω α)
    [IsProbabilityMeasure (volume : Measure Ω)] : PMF α := by
  -- show the pushforward is also a probability measure
  letI : IsProbabilityMeasure (law (Ω := Ω) (α := α) rv) := by
    refine ⟨by
      -- (map X volume) univ = volume (preimage univ) = volume univ = 1
      simp [law, Measure.map_apply rv.measurable_X MeasurableSet.univ]⟩
  exact (law rv).toPMF

-- Calculate P(Y|X)
noncomputable def conditional_PMF (X : DiscreteRV Ω α) (Y : DiscreteRV Ω β) [Nonempty β] :
 ProbabilityTheory.Kernel α β := by
  haveI : IsFiniteMeasure (volume : Measure Ω) := by infer_instance
  exact ProbabilityTheory.condDistrib
    (μ := (volume : Measure Ω))
    (X := X.X)
    (Y := Y.X)

-- Calculate joint random variable (X, Y)
noncomputable def discrete_joint_RV (X : DiscreteRV Ω α) (Y : DiscreteRV Ω β) :
DiscreteRV Ω (α × β) := by
  exact (DiscreteRV.mk (X := fun ω => (X.X ω, Y.X ω))
  (measurable_X := Measurable.prodMk X.measurable_X Y.measurable_X))

end DiscreteRV
