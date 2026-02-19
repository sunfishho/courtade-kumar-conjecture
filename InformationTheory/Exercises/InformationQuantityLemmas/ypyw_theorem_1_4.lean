import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.Discrete.DiscreteRandomVariable

-- Theorem 1.4 in Information Theory: From Coding to Learning

open DiscreteInformationQuantities DiscreteRandomVariable MeasureTheory ProbabilityTheory

variable {Ω S T : Type*}
  [MeasureSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace S] [StandardBorelSpace S] [Countable S] [MeasurableSingletonClass S] [Nonempty S]
  [MeasurableSpace T] [StandardBorelSpace T] [Countable T] [MeasurableSingletonClass T] [Nonempty T]
  [IsProbabilityMeasure (volume : Measure Ω)]

/-- entropy is positive -/
theorem entropy_positivity (X : DiscreteRandomVariable Ω S) : discrete_entropy X ≥ 0 := by
  sorry

/-- entropy is zero if and only if the random variable is deterministic -/
theorem entropy_zero (X : DiscreteRandomVariable Ω S) :
    discrete_entropy X = 0 ↔ ∃ s : S, X.PMF s = 1 := by
  sorry

/-- entropy is maximized by the uniform distribution -/
theorem entropy_max (X : DiscreteRandomVariable Ω S) [Fintype S] :
    discrete_entropy X ≤ discrete_entropy_given_PMF (PMF.uniformOfFintype S) := by
  sorry

/-- chain rule for entropy -/
theorem chain_rule_entropy (X : DiscreteRandomVariable Ω S) (Y : DiscreteRandomVariable Ω T) :
    discrete_entropy (discrete_joint_RV X Y)
      = discrete_entropy X + discrete_conditional_entropy (X := X) (Y := Y) := by
  sorry
