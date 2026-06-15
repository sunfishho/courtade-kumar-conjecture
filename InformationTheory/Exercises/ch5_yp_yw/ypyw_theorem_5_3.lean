import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 5.3 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω Ω₁: Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [StandardBorelSpace Ω] [StandardBorelSpace Ω₁] [Nonempty Ω] [Nonempty Ω₁]

-- mutual information is concave given fixed P_{Y|X} and convex given fixed P_X
theorem mutual_information_concavity_fixed_kernel (P_yx : Kernel Ω Ω₁) [IsMarkovKernel P_yx] (Px₁ Px₂: Measure Ω) [hP1 : IsProbabilityMeasure Px₁] [hP2 : IsProbabilityMeasure Px₂] (t : ℝ≥0∞) (ht : t ≤ 1) :
    let f : ProbabilityMeasure Ω → ℝ≥0∞ := fun P => mutual_information_kernel P.toMeasure P_yx
    haveI hPmix : IsProbabilityMeasure (t • Px₁ + (1 - t) • Px₂) := by
        constructor
        simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        exact add_tsub_cancel_of_le ht
    f ⟨t • Px₁ + (1 - t) • Px₂, hPmix⟩ ≥ t * f ⟨Px₁, hP1⟩ + (1 - t) * f ⟨Px₂, hP2⟩ := by
sorry

theorem mutual_information_convexity_fixed_measure (Px : Measure Ω) [IsProbabilityMeasure Px]
    (P_yx1 P_yx2 : Kernel Ω Ω₁) [hK1 : IsMarkovKernel P_yx1] [hK2 : IsMarkovKernel P_yx2]
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (K_mix : Kernel Ω Ω₁) [hKmix : IsMarkovKernel K_mix]
    (hmix : ∀ x, K_mix x = t • P_yx1 x + (1 - t) • P_yx2 x) :
    let f : { K : Kernel Ω Ω₁ // IsMarkovKernel K } → ℝ≥0∞ :=
        fun K => letI := K.2; mutual_information_kernel Px K.1
    f ⟨K_mix, hKmix⟩ ≤ t * f ⟨P_yx1, hK1⟩ + (1 - t) * f ⟨P_yx2, hK2⟩ := by
sorry
