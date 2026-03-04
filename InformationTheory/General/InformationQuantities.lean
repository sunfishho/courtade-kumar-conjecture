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

/-- conditional Kl divergence $D(P_{Y|X}||Q_{Y|X}|P_X)$, where $P,Q$ are over $Ω₁ × Ω₂$ and $X ∈ Ω₁, Y ∈ Ω₂$ -/
-- note that we don't need $Ω₁$ to be a standard Borel space because we are only conditioning on $Ω₂$
noncomputable def conditionalklDivBase2 {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [StandardBorelSpace Ω₂] [Nonempty Ω₂]
    (P Q : Measure (Ω₁ × Ω₂)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : ℝ≥0∞ :=
  ∫⁻ x,
      klDivBase2
        ((ProbabilityTheory.condDistrib (Y := Prod.snd) (X := Prod.fst) P) x)
        ((ProbabilityTheory.condDistrib (Y := Prod.snd) (X := Prod.fst) Q) x)
    ∂(P.fst)



-- I(P_X, P_{Y|X}) = D(P_{X,Y}||P_XP_Y)
-- should probably take in probability measures instead of measures
noncomputable def mutual_information (PQ : Measure (Ω₁ × Ω₂)) [IsProbabilityMeasure PQ] : ℝ≥0∞ :=
  let P := PQ.fst
  let Q := PQ.snd
  klDivBase2 PQ (P.prod Q)

noncomputable def differential_entropy {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (P : Measure S) [IsProbabilityMeasure P] : EReal :=
  -generalklDivBase2 (P.map (Subtype.val : S → EuclideanSpace ℝ (Fin n))) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)

end InformationQuantities
