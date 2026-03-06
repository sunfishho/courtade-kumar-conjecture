import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.Utilities

-- Theorem 3.16 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory Utilities

variable {d : ℕ}

/-- The entropy power of a ℝ^d-valued random variable with law P. -/
noncomputable def entropy_power
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] : ℝ :=
    letI : IsProbabilityMeasure
      (P.map (fun x => (⟨x, Set.mem_univ x⟩ : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin d)))))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
    let h : ℝ := (differential_entropy Set.univ
    (P.map (fun x => (⟨x, Set.mem_univ x⟩ : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin d))))))).toReal
    (2 * Real.pi * Real.exp 1)⁻¹ * Real.exp ((2 : ℝ) / (d : ℝ) * h)

-- EPI
theorem entropy_power_inequality
    (Pa1 Pa2 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure Pa1] [IsProbabilityMeasure Pa2] :
    -- because we are working with the measures, we can actually just assume independence by using the product measure
    let Pa_sum := (Pa1.prod Pa2).map (fun p => p.1 + p.2)
    haveI : IsProbabilityMeasure Pa_sum := Measure.isProbabilityMeasure_map (by fun_prop)
    -- check both measures have finite second moments
    MemLp id 2 Pa1 → MemLp id 2 Pa2 →
    entropy_power Pa_sum ≥ entropy_power Pa1 + entropy_power Pa2 := by
  sorry
