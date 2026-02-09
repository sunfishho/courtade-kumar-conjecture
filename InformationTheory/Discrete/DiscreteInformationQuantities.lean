import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.ProductMeasure
import InformationTheory.Discrete.DiscreteRandomVariable

import Mathlib


open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace DiscreteInformationQuantities

variable {Ω α β : Type*}
    [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]

-- H(X) := -∑_x P(x) log(P(x))
noncomputable def discrete_entropy
    (rv : DiscreteRandomVariable Ω α) : ℝ :=
  ∑' a : α, Real.negMulLog ((rv.PMF a).toReal) * (Real.logb 2 (exp 0))

-- H(Y|X) := ∑_x ∑_y P(y) P(x|y) log(P(x|y))
noncomputable def discrete_conditional_entropy
(X : DiscreteRandomVariable Ω α) (Y : DiscreteRandomVariable Ω β) [Nonempty β] : ℝ :=
  ∑' x : α, ∑' y : β,
    -(Y.PMF y).toReal * Real.negMulLog ((X.conditional_PMF Y) x {y}).toReal * (Real.logb 2 (exp 0))

-- I(X; Y) := H(X) - H(X|Y)
noncomputable def discrete_mutual_information [Nonempty β]
(X : DiscreteRandomVariable Ω α) (Y : DiscreteRandomVariable Ω β) : ℝ :=
  discrete_entropy X - discrete_conditional_entropy X Y

-- I(X; Y | Z) := H(X | Z) - H(X | Y, Z)
noncomputable def discrete_conditional_mutual_information
    {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [Countable γ] [Nonempty α] (X : DiscreteRandomVariable Ω α)
    (Y : DiscreteRandomVariable Ω α) (Z : DiscreteRandomVariable Ω α)
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
              * Real.logb 2 ((p s).toReal / (q s).toReal))


end DiscreteInformationQuantities
