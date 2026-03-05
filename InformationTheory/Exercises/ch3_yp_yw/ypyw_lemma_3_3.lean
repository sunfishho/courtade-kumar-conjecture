import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Lemma 3.3 in Information Theory: From Coding to Learning

open InformationQuantities DiscreteInformationQuantities MeasureTheory ProbabilityTheory

variable (X Y : Type*) [Countable X] [Countable Y] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y] [StandardBorelSpace X] [Nonempty Y]

theorem lemma_3_3 (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] :
  Pxy ≪ Pxy.fst.prod Pxy.snd ↔ ∀ᵐ x ∂Pxy.fst, Pxy.condKernel x ≪ Pxy.snd := by
sorry
