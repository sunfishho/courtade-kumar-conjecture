import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Proposition 1.5 in Information Theory: From Coding to Learning

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory

noncomputable def multinomial_coeff {k : ℕ} (n : Fin k → ℕ) : ℕ :=
  let N := ∑ i : Fin k, n i
  Nat.factorial N / ∏ i : Fin k, Nat.factorial (n i)

noncomputable def shannonEntropyNatLog {k : ℕ} (p : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, Real.negMulLog (p i) * (Real.logb 2 (Real.exp 1))

theorem method_of_types {k : ℕ} (n : Fin k → ℕ) :
    let N : ℕ := ∑ i : Fin k, n i
    let p : Fin k → ℝ := fun i => (n i : ℝ) / (N : ℝ)
    ((Real.exp (N * shannonEntropyNatLog p)) / ((1 + (N : ℝ))^(k-1)))
        ≤ (multinomial_coeff n : ℝ)
      ∧ (multinomial_coeff n : ℝ) ≤ Real.exp (N * shannonEntropyNatLog p) := by
  sorry
