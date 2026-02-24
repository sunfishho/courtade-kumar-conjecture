import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.ProductMeasure

import Mathlib


open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace DiscreteInformationQuantities

-- H(X) := -∑_x P(x) log(P(x))
noncomputable def discrete_entropy
    {α : Type*} [Countable α] (pmf : PMF α) : ℝ :=
  ∑' a : α, Real.negMulLog ((pmf a).toReal) * (Real.logb 2 (exp 1))

/-- Conditional entropy \(H(X|Y)\) from a joint PMF on `α × β`. -/
noncomputable def discrete_conditional_entropy
{α β : Type*} [Countable α] [Countable β] (joint_pmf : PMF (α × β)) : ℝ :=
  let y_pmf : PMF β := PMF.map Prod.snd joint_pmf
  let pX_givenY : β → α → ℝ≥0∞ :=
    fun y x => if y_pmf y = 0 then 0 else joint_pmf (x, y) / y_pmf y
  ∑' y : β,
    (y_pmf y).toReal
      * (∑' x : α, Real.negMulLog ((pX_givenY y x).toReal) * (Real.logb 2 (exp 1)))

/-- Dependent conditional entropy \(H(X|Y)\) from a joint PMF on a sigma type `Σ y, α y`. -/
noncomputable def dependent_discrete_conditional_entropy
    {β : Type*} {α : β → Type*} [Countable β] [∀ y : β, Countable (α y)]
    (joint_pmf : PMF (Sigma α)) : ℝ :=
  let y_pmf : PMF β := PMF.map (fun z : Sigma α => z.1) joint_pmf
  let pX_givenY : (y : β) → α y → ℝ≥0∞ :=
    fun y x => if y_pmf y = 0 then 0 else joint_pmf ⟨y, x⟩ / y_pmf y
  ∑' y : β,
    (y_pmf y).toReal
      * (∑' x : α y, Real.negMulLog ((pX_givenY y x).toReal) * (Real.logb 2 (exp 1)))

-- I(X;Y) := H(X) + H(Y) - H(X,Y)
noncomputable def discrete_mutual_information
    {α β : Type*} [Countable α] [Countable β] (joint_pmf : PMF (α × β)) : ℝ :=
  discrete_entropy (PMF.map Prod.fst joint_pmf)
    + discrete_entropy (PMF.map Prod.snd joint_pmf)
    - discrete_entropy joint_pmf

-- I(X;Y|Z) := H(X|Z) - H(X|Y,Z)
noncomputable def discrete_conditional_mutual_information
    {α β γ : Type*} [Countable α] [Countable β] [Countable γ] (joint_pmf : PMF (α × (β × γ))) : ℝ :=
  let joint_xz : PMF (α × γ) :=
    PMF.map (fun p : α × (β × γ) => (p.1, p.2.2)) joint_pmf
  discrete_conditional_entropy joint_xz - discrete_conditional_entropy joint_pmf

-- D(p || q) = ∑_x q(x) * p(x)/q(x) * log(p(x)/q(x))
-- Inputs are PMFs because we are in a discrete setting.
noncomputable def discrete_kl_divergence {S : Type*} [Countable S] (p q : PMF S) : ℝ≥0∞ := by
  by_cases h : ∃ s : S, q s = 0 ∧ p s ≠ 0
  -- ⊤ if the KL divergence is infinite
  · exact ⊤
  · exact
      ENNReal.ofReal
        (∑' s : S,
          if hq : q s = 0 then 0
          else
              (p s).toReal
              * Real.logb 2 ((p s).toReal / (q s).toReal))

end DiscreteInformationQuantities
