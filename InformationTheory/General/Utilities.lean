import Mathlib
open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal EReal

namespace Utilities


/-- Definition of submodularity for a function defined over subsets of a finite set S. -/
def submodular (α : Type*) [DecidableEq α] (S : Finset α) (f : {T : Finset α // T ⊆ S} → ℝ≥0∞) :
    Prop :=
  ∀ (T₁ T₂ : {T : Finset α // T ⊆ S}),
    f ⟨T₁.1 ∪ T₂.1, Finset.union_subset T₁.2 T₂.2⟩
      + f ⟨T₁.1 ∩ T₂.1, (Finset.inter_subset_left).trans T₁.2⟩
      ≤ f T₁ + f T₂

noncomputable def log2_EReal (b : ℝ≥0∞) : EReal :=
  if b = 0 then ⊥ else
  (ENNReal.log b) * (logb 2 (exp 1))

noncomputable def Log (a : ℝ≥0∞) (b : ℝ≥0∞) : EReal :=
  if a = 0 ∧ b > 0 then ⊥ else
  if a > 0 ∧ b = 0 then ⊤ else
  if a = 0 ∧ b = 0 then 0 else
  (ENNReal.log (a / b)) * (logb 2 (exp 1))


end Utilities
