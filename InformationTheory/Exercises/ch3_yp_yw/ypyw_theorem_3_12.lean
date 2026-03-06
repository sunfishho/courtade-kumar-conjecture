import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.General.Utilities

-- Theorem 3.12 in Information Theory: From Coding to Learning

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory Utilities ENNReal

variable {Ω Ω₁: Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω₁] [Finite Ω] [Finite Ω₁] [Nonempty Ω] [Nonempty Ω₁]
  (joint_pmf : PMF (Ω × Ω₁ × Ω))

theorem fanos_inequality :
    let M : ℕ := Nat.card Ω
    let X_pmf := joint_pmf.map Prod.fst
    let X'_pmf := (joint_pmf.map Prod.snd).map Prod.snd
    let XX'_pmf := joint_pmf.map (fun p : Ω × Ω₁ × Ω => (p.1, p.2.2))
    let XY_pmf := joint_pmf.map (fun p : Ω × Ω₁ × Ω => (p.1, p.2.1))
    let Pe : ℝ := 1 - (∑' x : Ω, (XX'_pmf (x, x))).toReal
    let F_M := fun p : ℝ => (1 - p) * Real.logb 2 ((M : ℝ) - 1) + bin_entropy p
    let P_max : ℝ := (⨆ x : Ω, X_pmf x).toReal
    -- X <-> Y <-> X' implies that H(X|Y) ≤ F_M(1-P_e)
    (isMarkovChain joint_pmf.toMeasure) → ((discrete_conditional_entropy XY_pmf).toReal ≤ (F_M (1 - Pe))
    -- and if P_max is the maximum value of P_x, then I(X; Y) ≥ (1 - P_e)log (1/P_max) - h(P_e)
    ∧ (discrete_mutual_information XY_pmf).toReal ≥ (1 - Pe) * (Real.logb 2 (1 / Pe)) - bin_entropy Pe) :=
    by sorry
