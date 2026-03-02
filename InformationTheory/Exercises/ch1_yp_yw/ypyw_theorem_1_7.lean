import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Theorem 1.7 in Information Theory: From Coding to Learning (Han's inequality)
-- Cursor-aided

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory

variable {S : Type*} [Countable S]

noncomputable def indices_to_entropy {n : ℕ+} (joint_pmf : PMF (Fin n → S))
    (indices_subset : Finset (Fin n)) : ℝ :=
  (discrete_entropy <|
    PMF.map
      (fun x : Fin n → S =>
        (fun i : (↑indices_subset) => x i.1))
      joint_pmf).toReal

-- note that 1 ≤ k ≤ n
noncomputable def avg_entropy_k_subset_coords {n : ℕ+} (k : ℕ) (joint_pmf : PMF (Fin n → S)):
    ℝ :=
  (Finset.sum ((Finset.univ : Finset (Fin n)).powersetCard (k : ℕ)) fun indices_subset =>
        indices_to_entropy joint_pmf indices_subset) /
    (Nat.choose (n : ℕ) (k : ℕ) : ℝ)

/-- Han's inequality -/
theorem hans_inequality {n : ℕ+} (joint_pmf : PMF (Fin n → S)) :
  (∀ k₁ k₂ : ℕ,
      (0 < k₁ ∧ k₁ < k₂ ∧ k₂ ≤ n) → 1 / (k₁ : ℝ) * avg_entropy_k_subset_coords k₁ joint_pmf
        ≥
        1 / ((k₂ : ℕ) + 1 : ℝ) * avg_entropy_k_subset_coords k₂ joint_pmf) ∧
    (∀ k₁ k₂ k₃ : ℕ,
        (k₁ = k₂ + 1) → (k₂ = k₃ + 1) → avg_entropy_k_subset_coords k₁ joint_pmf
          - avg_entropy_k_subset_coords k₂ joint_pmf
        ≤
        avg_entropy_k_subset_coords k₂ joint_pmf - avg_entropy_k_subset_coords k₃ joint_pmf) := by
  sorry
