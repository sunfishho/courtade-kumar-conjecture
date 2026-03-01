import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.Discrete.DiscreteInformationQuantities
import Mathlib.Probability.Kernel.Defs

open ProbabilityTheory MeasureTheory DiscreteInformationQuantities ENNReal

namespace TypicalSequences

variable {Ω S : Type*} [MeasurableSpace S]
[StandardBorelSpace S]
[Countable S] [MeasurableSingletonClass S] (x_pmf : PMF S)

-- compute the iid likelihood of sequence S
noncomputable def sequence_likelihood
(PMF : PMF S) {N : ℕ+}
(realizations : Fin N → S) : ℝ := ∏ i : Fin N, (PMF (realizations i)).toReal

-- we restrict ε to be positive
-- Set of all sequences satisfying |1/n * (log (1/P(x^n) - H(X)))| < ε
-- We restrict the entropy to be finite.
noncomputable def eps_typical {n : ℕ+} (ε : ℝ)
(realization : (Fin n → S)) : Prop :=
0 < ε ∧
(discrete_entropy x_pmf = ∞ → False) ∧
Real.nnabs (((Real.logb 2
(1/(sequence_likelihood x_pmf realization))) / (n : ℝ)) - (discrete_entropy x_pmf).toReal) < ε

noncomputable def eps_typical_set (ε : ℝ) {n : ℕ+} : Set (Fin n → S) :=
  {x | eps_typical x_pmf ε x}

end TypicalSequences
