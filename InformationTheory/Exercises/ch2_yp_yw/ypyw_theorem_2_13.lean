import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 2.13 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable (X Y : Type*) [Countable X] [MeasurableSpace X] [MeasurableSpace Y] (Pyx : Kernel X Y) (Qyx : Kernel X Y) [IsMarkovKernel Pyx] [IsMarkovKernel Qyx] [StandardBorelSpace Y]

theorem measurability_lemma : MeasurableSet {x : X | Pyx x ≪ Qyx x} ∧ Measurable (fun x => klDivBase2 (Pyx x) (Qyx x)):= by
sorry
