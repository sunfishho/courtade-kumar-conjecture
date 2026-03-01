import Mathlib
open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Utilities

open ENNReal

/-- Definition of submodularity for a function defined over subsets of a finite set S. -/
def submodular (α : Type*) [DecidableEq α] (S : Finset α) (f : {T : Finset α // T ⊆ S} → ℝ≥0∞) :
    Prop :=
  ∀ (T₁ T₂ : {T : Finset α // T ⊆ S}),
    f ⟨T₁.1 ∪ T₂.1, Finset.union_subset T₁.2 T₂.2⟩
      + f ⟨T₁.1 ∩ T₂.1, (Finset.inter_subset_left).trans T₁.2⟩
      ≤ f T₁ + f T₂

end Utilities
