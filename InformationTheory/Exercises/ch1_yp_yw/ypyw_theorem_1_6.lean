import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.Discrete.Utilities

-- Theorem 1.6 in Information Theory: From Coding to Learning

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory

variable {S : Type*} [Countable S]

/-- entropy is a submodular function -/
theorem entropy_submodularity {n : ℕ+} (joint_pmf : PMF (Fin n → S)) :
    Utilities.submodular (Fin n) Finset.univ
      (fun T =>
        discrete_entropy
          (PMF.map
            -- map any distribution over S^n by projecting it onto the coordinates corresponding to T
            (fun x : Fin n → S =>
              (fun i : (↑(T.1)) => x i.1))
            joint_pmf)) := by
  sorry
