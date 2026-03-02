import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Theorem 1.7 in Information Theory: From Coding to Learning (Han's inequality)

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory

variable {S : Type*} [Finite S] [Nonempty S]

/-- Shearer's lemma -/
theorem shearers_lemma {n : ℕ+} (joint_pmf : PMF ((Fin n → S) × Finset (Fin n))):
  let xn_pmf : PMF (Fin n → S) := PMF.map Prod.fst joint_pmf
  let s_pmf : PMF (Finset (Fin n)) := PMF.map Prod.snd joint_pmf
  let min_s_pmf : ENNReal := Finset.min'
    ((Finset.univ : Finset (Finset (Fin n))).image (fun s => s_pmf s))
    (by simp)
  let xs_s_pmf : PMF (Σ s : Finset (Fin n), s → S) :=
  PMF.map
    (fun p : (Fin n → S) × Finset (Fin n) =>
      ⟨p.2, fun i : p.2 => p.1 i.1⟩)
    joint_pmf
  ∀ x : (Fin n → S), ∀ s : Finset (Fin n), joint_pmf (x, s) = xn_pmf x * s_pmf s →
  dependent_discrete_conditional_entropy xs_s_pmf ≥ discrete_entropy xn_pmf * min_s_pmf := by
  sorry
