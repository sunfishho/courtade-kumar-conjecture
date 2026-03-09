import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 5.1 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P₁ P₂ Q₁ Q₂: Measure Ω) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]

-- D(P || Q) is convex in (P, Q)
theorem kl_is_convex_in_pair (t : ℝ≥0∞) (ht : t ≤ 1) :
  haveI hPmix : IsProbabilityMeasure (t • P₁ + (1 - t) • P₂) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le ht
  haveI hQmix : IsProbabilityMeasure (t • Q₁ + (1 - t) • Q₂) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le ht
  t * klDivBase2 P₁ Q₁ + (1 - t) * klDivBase2 P₂ Q₂ ≥
  klDivBase2 (t • P₁ + (1 - t) • P₂) (t • Q₁ + (1 - t) • Q₂) := by
sorry
