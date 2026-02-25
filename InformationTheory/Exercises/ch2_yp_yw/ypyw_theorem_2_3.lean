import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 2.3 in Information Theory: From Coding to Learning

open MeasureTheory InformationQuantities

theorem nonnegativity_kl_divergence {Ω : Type*} [MeasureSpace Ω] [StandardBorelSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
  klDivBase2 P Q ≥ 0 := by
  sorry
