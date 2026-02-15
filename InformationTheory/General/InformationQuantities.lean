import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.General.RandomVariable
import Mathlib.Probability.Kernel.Defs
import Mathlib.InformationTheory.KullbackLeibler.Basic

import Mathlib

open ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace InformationQuantities

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

-- I(P_X, P_{Y|X}) = D(P_{X,Y}||P_XP_Y)
-- should probably take in probability measures instead of measures
noncomputable def mutual_information (PQ : Measure (Ω₁ × Ω₂)) : ℝ≥0∞ :=
  let P := PQ.fst
  let Q := PQ.snd
  InformationTheory.klDiv PQ (P.prod Q)

end InformationQuantities
