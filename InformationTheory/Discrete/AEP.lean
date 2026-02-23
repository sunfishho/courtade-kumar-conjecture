import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.Discrete.TypicalSequences

open MeasureTheory
open TypicalSequences
open DiscreteInformationQuantities

namespace AEP

variable {S : Type*} [MeasurableSpace S]
  [Countable S] [MeasurableSingletonClass S] [StandardBorelSpace S]
  (x_pmf : PMF S)

noncomputable def iid_probMeasure (n : ℕ+) : MeasureTheory.ProbabilityMeasure (Fin n → S) :=
  MeasureTheory.ProbabilityMeasure.pi (α := fun _ : Fin n => S)
    (fun _ : Fin n => (⟨x_pmf.toMeasure, inferInstance⟩ : MeasureTheory.ProbabilityMeasure S))

noncomputable def iid_PMFs (n : ℕ+) : PMF (Fin n → S) :=
  (iid_probMeasure x_pmf n).toMeasure.toPMF

/-- Probability of a realization of iid draws from X being ε-typical. -/
noncomputable def prob_typical (ε : ℝ) (n : ℕ+) : ENNReal :=
  (iid_probMeasure x_pmf n).toMeasure (eps_typical_set x_pmf ε (n := n))

/-- -1/n * log_2(P(x^n)) for a concrete realization x^n -/
noncomputable def aep_term_realization (n : ℕ+) (realization : Fin n → S) : ℝ :=
  (- (1 : ℝ) / (n : ℝ)) *
    Real.logb 2 (sequence_likelihood x_pmf realization)

/-- The i.i.d. law of the length-`n` sample `(X₁, …, Xₙ)` as a measure on realizations
`Fin n → S`. -/
noncomputable def iid_sample_law (n : ℕ+) : Measure (Fin n → S) :=
  (iid_probMeasure x_pmf n).toMeasure

/-- AEP: under the i.i.d. law of `X^n`, the quantity `aep_term_realization` converges in probability
to `discrete_entropy X` as `n → ∞`. -/
theorem AEP_converges_in_probability :
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun n : ℕ+ =>
        iid_sample_law (S := S) x_pmf n
          {x | ε < Real.nnabs (aep_term_realization x_pmf n x - discrete_entropy x_pmf)})
      Filter.atTop (nhds (0 : ENNReal)) :=
  sorry

-- Cover and Thomas, Theorem 3.1.2: the probability of a realization of iid draws from `X`
-- being ε-typical converges to 1 as `n → ∞`.
lemma prob_typical_lem (ε : ℝ) (hε : 0 < ε) :
  Filter.Tendsto (fun n : ℕ+ => prob_typical x_pmf ε n) Filter.atTop (nhds (1 : ENNReal)) :=
by
  sorry

end AEP
