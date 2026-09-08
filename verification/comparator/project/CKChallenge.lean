import InformationTheory.CourtadeKumar.Basic

/- Comparator challenge only: the two sorry bodies specify the requested
   statements; they are never permitted in the solution environment.
   Statement is copied from the existing mathematical interface, independently
   of the completed proof and all four certificate families. -/
namespace CourtadeKumar
open scoped ENNReal NNReal

def Statement : Prop :=
  ∀ (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1 / 2) (b : BitVec n → Bool),
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one halpha) b).toMeasure
      ≤ ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ))

theorem courtadeKumar_via_completed_certificates : Statement := by
  sorry

theorem mutual_information_le_capacity_via_completed_certificates
    (n : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1/2) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one ha) b).toMeasure ≤
      ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) := by
  sorry

end CourtadeKumar
