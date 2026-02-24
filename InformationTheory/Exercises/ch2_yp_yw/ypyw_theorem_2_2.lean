import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Theorem 2.2 in Information Theory: From Coding to Learning

open InformationTheory MeasureTheory ProbabilityTheory DiscreteInformationQuantities

/-- Entropy vs divergence-/
theorem entropy_divergence_uniform_relation {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [StandardBorelSpace α] (P : Measure α) [IsProbabilityMeasure P] :
  let uniform_dist : Measure α := (PMF.uniformOfFintype α).toMeasure
  discrete_entropy P.toPMF = Real.logb 2 (Fintype.card α) - (klDiv P uniform_dist).toReal := by
  sorry
