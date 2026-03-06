import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Theorem 3.11 in Information Theory: From Coding to Learning

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω] [Nonempty Ω]
  (joint_pmf : PMF (Ω × Ω))

-- H(X) ≤ F_M(P[X=X']) when X ⊥ X', and H(X) ≤ F_M(P_max) always,
-- with equality iff X_pmf has P_max as one entry and is uniform on the rest
theorem entropy_bound_by_uncertainty :
    let X_pmf := joint_pmf.map Prod.fst
    let X'_pmf := joint_pmf.map Prod.snd
    let M : ℕ := Nat.card Ω
    let F_M := fun p : ℝ => (1 - p) * Real.logb 2 ((M : ℝ) - 1) + bin_entropy p
    let P_X_is_X' : ℝ := ∑' x : Ω, (joint_pmf (x, x)).toReal
    let P_max : ℝ := (⨆ x : Ω, X_pmf x).toReal
    -- independence implies H(X) ≤ F_M(P[X = X']) and everything else
    (joint_pmf.toMeasure = X_pmf.toMeasure.prod X'_pmf.toMeasure) →
      ((discrete_entropy X_pmf).toReal ≤ F_M P_X_is_X'
    -- H(X) ≤ F_M(P_max) always
    ∧ (discrete_entropy X_pmf).toReal ≤ F_M P_max
    -- equality iff X_pmf takes value P_max at some x₀ and is uniform with value (1-P_max)/(M-1) on the rest
    ∧ ((discrete_entropy X_pmf).toReal = F_M P_max ↔
        ∃ x₀ : Ω, X_pmf x₀ = ENNReal.ofReal P_max ∧
          ∀ x : Ω, x ≠ x₀ → X_pmf x = ENNReal.ofReal ((1 - P_max) / ((M : ℝ) - 1)))) :=
  by sorry
