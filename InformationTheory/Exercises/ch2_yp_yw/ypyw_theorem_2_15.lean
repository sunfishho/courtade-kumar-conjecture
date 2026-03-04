import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 2.13 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [StandardBorelSpace X]

theorem kl_chain_rule (P : Measure (X × Y)) (Q : Measure (X × Y)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [Nonempty Y] :
  klDivBase2 P Q = conditionalklDivBase2 P Q + klDivBase2 (P.fst) (Q.fst) := by
  sorry
