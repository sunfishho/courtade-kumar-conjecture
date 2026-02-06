import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import InformationTheory.Discrete.DiscreteRandomVariable
import InformationTheory.Discrete.DiscreteInformationQuantities
import Mathlib.Probability.Kernel.Defs

open ProbabilityTheory
open MeasureTheory
open DiscreteInformationQuantities

namespace TypicalSequences

variable {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S]
[IsProbabilityMeasure (volume : Measure Ω)]
[Countable S] [MeasurableSingletonClass S] (X : DiscreteRandomVariable Ω S)

-- compute the iid likelihood of sequence S
noncomputable def sequence_likelihood
(PMF : PMF S) (N : ℕ+)
(realizations : Vector S N) : ℝ := ∏ i : Fin N, (PMF (realizations.get i)).toReal

-- we restrict ε to be positive
-- Set of all sequences satisfying |1/n * (log (1/P(x^n) - H(X)))| < ε
noncomputable def eps_typical_set (N : ℕ+) (ε : ℝ)
(realizations : Vector S N) : Prop :=
0 < ε ∧
Real.nnabs ((Real.logb 2
(1/(sequence_likelihood X.PMF N realizations))) / N - discrete_entropy X) < ε

end TypicalSequences
