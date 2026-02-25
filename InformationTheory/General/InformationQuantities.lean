import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.General.RandomVariable
import Mathlib

open ProbabilityTheory InformationTheory
open MeasureTheory
open scoped ENNReal

namespace InformationQuantities

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
[StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]

noncomputable def klDivBase2 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P Q : Measure Ω) : ℝ≥0∞ :=
  klDiv P Q * (ENNReal.ofReal (Real.logb 2 (Real.exp 1)))

-- I(P_X, P_{Y|X}) = D(P_{X,Y}||P_XP_Y)
-- should probably take in probability measures instead of measures
noncomputable def mutual_information (PQ : ProbabilityMeasure (Ω₁ × Ω₂)) : ℝ≥0∞ :=
  let P := PQ.toMeasure.fst
  let Q := PQ.toMeasure.snd
  klDivBase2 PQ.toMeasure (P.prod Q)

end InformationQuantities
