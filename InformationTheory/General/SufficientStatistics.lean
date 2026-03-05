import Mathlib

open MeasureTheory ProbabilityTheory


namespace SufficientStatistic

variable {Θ Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] (Px : Θ → Measure Ω₁) (T : Ω₁ → Ω₂) (hT : Measurable T) (hPx : ∀ θ, IsProbabilityMeasure (Px θ))

/-- T is a sufficient statistic of X for Θ-/
def sufficient_statistic : Prop :=
  let Ptx := Kernel.deterministic T hT
  let Pt := fun θ : Θ => (Px θ).map T
  ∃ Pxt : Kernel Ω₂ Ω₁, IsMarkovKernel Pxt ∧ ∀ θ : Θ, (Px θ).compProd Ptx = ((Pt θ).compProd Pxt).map Prod.swap

end SufficientStatistic
