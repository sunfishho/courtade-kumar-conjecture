import Mathlib

-- Theorem 2.3 in Information Theory: From Coding to Learning

open InformationTheory MeasureTheory

theorem nonnegativity_kl_divergence {Ω : Type*} [MeasureSpace Ω] [StandardBorelSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
  klDiv P Q ≥ 0 := by
  sorry
