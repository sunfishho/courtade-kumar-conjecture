import Mathlib
open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal EReal

namespace Utilities

set_option maxHeartbeats 0

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

/-- EReal-valued expectation, defined as the difference of the positive and negative parts. This should handle the infities correctly.-/
noncomputable def ereal_expect {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) (f : Ω → EReal) : EReal :=
  (ENNReal.toEReal (∫⁻ ω, (f ω).toENNReal ∂P))
    - (ENNReal.toEReal (∫⁻ ω, (-f ω).toENNReal ∂P))

def isMarkovChain {Ω₁ Ω₂ Ω₃ : Type*}
    [MeasurableSpace Ω₁] [StandardBorelSpace Ω₁]
    [MeasurableSpace Ω₂] [StandardBorelSpace Ω₂]
    [MeasurableSpace Ω₃] [StandardBorelSpace Ω₃]
    (Pxyz : Measure (Ω₁ × Ω₂ × Ω₃)) [IsProbabilityMeasure Pxyz] : Prop :=
  let mY : MeasurableSpace (Ω₁ × Ω₂ × Ω₃) := ‹MeasurableSpace Ω₂›.comap (fun p => p.2.1)
  let mX : MeasurableSpace (Ω₁ × Ω₂ × Ω₃) := ‹MeasurableSpace Ω₁›.comap Prod.fst
  let mZ : MeasurableSpace (Ω₁ × Ω₂ × Ω₃) := ‹MeasurableSpace Ω₃›.comap (fun p => p.2.2)
  CondIndep mY mX mZ (measurable_fst.comp measurable_snd).comap_le (μ := Pxyz)

end Utilities
