import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.General.SufficientStatistics
import InformationTheory.General.Utilities

-- Theorem 3.10 in Information Theory: From Coding to Learning

open MeasureTheory ProbabilityTheory SufficientStatistic ENNReal

variable {Θ Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] (Px : Θ → Measure Ω₁) (T : Ω₁ → Ω₂) (hT : Measurable T) (hPx : ∀ θ, IsProbabilityMeasure (Px θ))

theorem fisher_factorization (μ : Measure Ω₁) :
    (∀ θ : Θ, Px θ ≪ μ) →
        (sufficient_statistic (Px := Px) (T := T) (hT := hT)
        ↔ ∃ (g : Θ → Ω₂ → ℝ≥0∞) (h : Ω₁ → ℝ≥0∞),
            Measurable h ∧ (∀ θ, Measurable (g θ)) ∧
            ∀ θ : Θ, ∀ᵐ x ∂μ, (Px θ).rnDeriv μ x = g θ (T x) * h x) :=
by sorry
