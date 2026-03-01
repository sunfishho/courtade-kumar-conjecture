import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.Utilities

-- Lemma 2.5 in Information Theory: From Coding to Learning

open MeasureTheory InformationQuantities Utilities
open scoped ENNReal EReal


variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Properties of Log function -/
lemma Log_fn_properties
    (μ P Q R : Measure Ω)
    (hP : P ≪ μ) (hQ : Q ≪ μ) (hR : R ≪ μ) :
    ((InformationQuantities.klDivBase2 P Q ≠ ∞ ∨ InformationQuantities.klDivBase2 P R ≠ ∞) →
        ereal_expect P (fun ω =>
          Utilities.Log (Measure.rnDeriv R μ ω) (Measure.rnDeriv Q μ ω))
          =
          ENNReal.toEReal (InformationQuantities.klDivBase2 P Q)
            - ENNReal.toEReal (InformationQuantities.klDivBase2 P R) ) ∧
    (ENNReal.toEReal (InformationQuantities.klDivBase2 P Q)
        =
        ereal_expect P (fun ω =>
          Utilities.Log (Measure.rnDeriv P μ ω) (Measure.rnDeriv Q μ ω))) ∧
    (P ≪ Q →
        ENNReal.toEReal (InformationQuantities.klDivBase2 P Q)
          =
          ereal_expect P (fun ω =>
            Utilities.Log (Measure.rnDeriv P Q ω) 1)) := by
  sorry
