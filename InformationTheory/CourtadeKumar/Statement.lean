import InformationTheory.CourtadeKumar.Basic

open scoped ENNReal NNReal

namespace CourtadeKumar

/--
The Courtade--Kumar "most informative Boolean function" statement for the BSC.

Both `mutual_information` and `binaryEntropyBits` are measured in bits. The left side is kept in
`ℝ≥0∞`; embedding the finite real-valued right side with `ENNReal.ofReal` avoids losing information
by applying `ENNReal.toReal` before finiteness is proved.
-/
def Statement : Prop :=
  ∀ (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1 / 2) (b : BitVec n → Bool),
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one halpha) b).toMeasure
      ≤ ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ))

/-- Proof target. This theorem is the single intentional placeholder at the statement milestone. -/
theorem courtadeKumar : Statement := by
  sorry

end CourtadeKumar
