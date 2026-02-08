import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.Discrete.TypicalSequences

open ProbabilityTheory
open MeasureTheory
open TypicalSequences
open RandomVariable
open DiscreteInformationQuantities
open DiscreteRandomVariable

namespace AEP

variable {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S]
[IsProbabilityMeasure (volume : Measure Ω)] [Countable S] [MeasurableSingletonClass S]
(X : DiscreteRandomVariable Ω S)

/-- Probability of a realization of iid draws from X being ε-typical. -/
noncomputable def prob_typical (X : DiscreteRandomVariable Ω S) (ε : ℝ) (n : ℕ+) : ENNReal :=
  (iid_joint_RVs X.toRandomVariable).law.toMeasure (eps_typical_set X ε (n := n))

/-- -1/n * log_2(P(x^n)) for a concrete realization x^n -/
noncomputable def aep_term_realization (n : ℕ+) (realization : Fin n → S) : ℝ :=
  (- (1 : ℝ) / (n : ℝ)) *
    Real.logb 2 (discrete_sequence_likelihood X realization).toReal

/-- The i.i.d. law of the length-`n` sample `(X₁, …, Xₙ)` as a measure on realizations
`Fin n → S`. -/
noncomputable def iid_sample_law (n : ℕ+) : Measure (Fin n → S) :=
  (iid_joint_RVs (n := (n : ℕ)) X.toRandomVariable).law.toMeasure

/-- AEP: under the i.i.d. law of `X^n`, the quantity `aep_term_realization` converges in probability
to `discrete_entropy X` as `n → ∞`. -/
theorem AEP_converges_in_probability :
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun n : ℕ+ =>
        iid_sample_law (Ω := Ω) (S := S) X n
          {x | ε < Real.nnabs (aep_term_realization X n x - discrete_entropy X)})
      Filter.atTop (nhds (0 : ENNReal)) :=
  sorry


-- Cover and Thomas, Theorem 3.1.2: the probability of a realization of iid draws from `X`
-- being ε-typical converges to 1 as `n → ∞`.
lemma prob_typical_lem (ε : ℝ) (hε : 0 < ε) :
  Filter.Tendsto (fun n : ℕ+ => prob_typical X ε n) Filter.atTop (nhds (1 : ENNReal)) :=
by
  sorry

end AEP
