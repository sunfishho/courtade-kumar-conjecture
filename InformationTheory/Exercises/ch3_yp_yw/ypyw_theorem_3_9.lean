import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.General.SufficientStatistics
import InformationTheory.General.Utilities

-- Theorem 3.9 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory SufficientStatistic Utilities

variable (Θ Ω₁ Ω₂ : Type*) [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] [Nonempty Ω₁] (P_θx : Kernel Θ Ω₁) [IsMarkovKernel P_θx] (T : Ω₁ → Ω₂) (hT : Measurable T)

/-- TFAE: T is a suff. stat. of X for θ, ∀ P_θ, θ → T → X, ∀ P_θ, I(θ; X|T) = 0, ∀ P_θ, I(θ;X)=I(θ; T), -/
theorem equivalent_defs_suff_stats :
    sufficient_statistic (Px := P_θx) (T := T) (hT := hT)
    ↔ ∀ (Pθ : Measure Θ) [IsProbabilityMeasure Pθ],
        letI : IsProbabilityMeasure ((Pθ.compProd P_θx).map (fun p : Θ × Ω₁ => (p.1, p.2, T p.2))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
        isMarkovChain ((Pθ.compProd P_θx).map (fun p : Θ × Ω₁ => (p.1, p.2, T p.2)))
    ↔ ∀ (Pθ : Measure Θ) [IsProbabilityMeasure Pθ],
        letI : IsProbabilityMeasure ((Pθ.compProd P_θx).map (fun p : Θ × Ω₁ => (p.1, p.2, T p.2))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
        conditional_mutual_information ((Pθ.compProd P_θx).map (fun p : Θ × Ω₁ => (p.1, p.2, T p.2))) = 0
    ↔ ∀ (Pθ : Measure Θ) [IsProbabilityMeasure Pθ],
        letI : IsProbabilityMeasure ((Pθ.compProd P_θx).map (fun p : Θ × Ω₁ => (p.1, T p.2))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
        mutual_information (Pθ.compProd P_θx) =
        mutual_information ((Pθ.compProd P_θx).map (fun p : Θ × Ω₁ => (p.1, T p.2))) :=
by sorry
