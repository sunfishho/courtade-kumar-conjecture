import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProductMeasure
import InformationTheory.RandomVariable

import Mathlib

namespace BasicDiscreteDefinitions

open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

-- H(X) := -∑_x P(x) log(P(x))
noncomputable def discrete_entropy
    {Ω : Type u} {α : Type v}
    [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (rv : DiscreteRV Ω α) : ℝ :=
  ∑' a : α, Real.negMulLog ((rv.PMF a).toReal)

-- H(Y|X) := ∑_x ∑_y P(y) P(x|y) log(P(x|y))
noncomputable def discrete_conditional_entropy [MeasureSpace Ω]
[IsProbabilityMeasure (volume : Measure Ω)] [MeasurableSpace α] [Countable α]
[MeasurableSingletonClass α] [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
(X : DiscreteRV Ω α) (Y : DiscreteRV Ω β) [Nonempty β] : ℝ :=
  ∑' x : α, ∑' y : β,
    -(Y.PMF y).toReal * Real.negMulLog ((X.conditional_PMF Y) x {y}).toReal

-- I(X; Y) := H(X) - H(X|Y)
noncomputable def discrete_mutual_information [MeasureSpace Ω] [MeasurableSpace α]
[MeasurableSpace β] [IsProbabilityMeasure (volume : Measure Ω)] [Countable α] [Countable β]
[MeasurableSingletonClass α] [MeasurableSingletonClass β] [Nonempty β]
(X : DiscreteRV Ω α) (Y : DiscreteRV Ω β) : ℝ :=
  discrete_entropy X - discrete_conditional_entropy X Y

-- I(X; Y | Z) := H(X | Z) - H(X | Y, Z)
noncomputable def discrete_conditional_mutual_information
    {Ω α β γ : Type*}
    [MeasureSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    [Countable α] [Countable β] [Countable γ][IsProbabilityMeasure (volume : Measure Ω)] [Nonempty α]
    (X : DiscreteRV Ω α) (Y : DiscreteRV Ω α) (Z : DiscreteRV Ω α)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : ℝ :=
  discrete_conditional_entropy X Z - discrete_conditional_entropy X (Y.discrete_joint_RV Z)

-- D(p || q) = ∑_x q(x) * p(x)/q(x) * log(p(x)/q(x))
-- Inputs are PMFs because we are in a discrete setting.
noncomputable def discrete_kl_divergence {S : Type*} [Countable S] (p q : PMF S) : ℝ≥0∞ := by
  by_cases h : ∃ s : S, q s = 0 ∧ p s ≠ 0
  -- ⊤ if the KL divergence is infinite
  · exact ⊤
  · exact
      ENNReal.ofReal
        (∑' s : S,
          if hq : q s = 0 then 0
          else
              (p s).toReal
              * Real.log ((p s).toReal / (q s).toReal))


end BasicDiscreteDefinitions
