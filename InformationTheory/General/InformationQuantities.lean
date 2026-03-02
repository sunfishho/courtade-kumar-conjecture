import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.General.RandomVariable
import Mathlib

open ProbabilityTheory InformationTheory
open MeasureTheory
open scoped ENNReal

namespace InformationQuantities

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
[StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]

/-- Kl divergence between two probability measures-/
noncomputable def klDivBase2 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]: ℝ≥0∞ :=
  klDiv P Q * (ENNReal.ofReal (Real.logb 2 (Real.exp 1)))

/-- Kl divergence between two measures, not necessarily probability measures-/
noncomputable def generalklDivBase2 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P Q : Measure Ω) : EReal :=
  klDiv P Q * (ENNReal.ofReal (Real.logb 2 (Real.exp 1)))

-- I(P_X, P_{Y|X}) = D(P_{X,Y}||P_XP_Y)
-- should probably take in probability measures instead of measures
noncomputable def mutual_information (PQ : ProbabilityMeasure (Ω₁ × Ω₂)) : ℝ≥0∞ :=
  let P := PQ.toMeasure.fst
  let Q := PQ.toMeasure.snd
  klDivBase2 PQ.toMeasure (P.prod Q)

noncomputable def differential_entropy {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    [MeasurableSpace S] [StandardBorelSpace S] (P : Measure S) : EReal :=
      -generalklDivBase2 (P.map (Subtype.val : S → EuclideanSpace ℝ (Fin n)))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)

end InformationQuantities
