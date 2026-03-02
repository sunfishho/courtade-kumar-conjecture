import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.General.InformationQuantities

-- Theorem 2.2 in Information Theory: From Coding to Learning

open MeasureTheory ProbabilityTheory DiscreteInformationQuantities InformationQuantities

/-- Entropy vs divergence-/
theorem entropy_divergence_uniform_relation {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [StandardBorelSpace α] (P : Measure α) [IsProbabilityMeasure P] :
  let uniform_dist : Measure α := (PMF.uniformOfFintype α).toMeasure
  (discrete_entropy P.toPMF).toReal = Real.logb 2 (Fintype.card α) - (klDivBase2 P uniform_dist).toReal := by
  sorry
