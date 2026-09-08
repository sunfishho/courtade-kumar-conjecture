import InformationTheory.CourtadeKumar.CapacityClosure
import InformationTheory.CourtadeKumar.EnergyPositivity

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

/-- The exact remaining scalar interface: a Bellman step at every admissible
BSC parameter implies the full measure-theoretic statement. -/
theorem courtadeKumar_of_bellmanStep
    (hstep : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      BooleanBellmanStep alpha) : Statement := by
  intro n alpha halpha b
  exact bscMutualInformation_le_capacity_of_step alpha halpha
    (hstep alpha halpha) n b

/-- Equivalently, it suffices to prove the ordered equal-multiplier
assertion.  Sorting dominance has already been discharged from concavity of
the explicit envelope. -/
theorem courtadeKumar_of_orderedEqualMultiplier
    (hordered : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedEqualMultiplierBellmanStep alpha) : Statement := by
  apply courtadeKumar_of_bellmanStep
  intro alpha halpha
  exact booleanBellmanStep_of_orderedEqualMultiplier alpha
    (hordered alpha halpha) (bellmanEnvelopeSortingDominance alpha halpha)

end CourtadeKumar
