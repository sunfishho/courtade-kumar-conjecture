import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.ProbabilityProjectionProofs

-- Corollary 4.2 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [StandardBorelSpace Ω] [StandardBorelSpace Ω₁] [Nonempty Ω] [Nonempty Ω₁] (Pxy : Measure (Ω × Ω₁)) [IsProbabilityMeasure Pxy]

-- For any Q_Y, I(X;Y) ≤ D(P_{Y|X} || Q_Y | P_X), and so I(X;Y) = min_{Q_Y} D(P_{Y|X} || Q_Y | P_X), with a unique minimizer of Q_Y = P_Y if we have finite MI
theorem mutual_information_distance_to_product :
    let Px : Measure Ω := Pxy.map (fun p : Ω × Ω₁ => p.1)
    let Py : Measure Ω₁ := Pxy.map (fun p : Ω × Ω₁ => p.2)
    (mutual_information Pxy = ⨅ (Qy : ProbabilityMeasure Ω₁),
      klDivBase2 Pxy (Px.prod Qy.toMeasure)) ∧
    ∀ (Qy : ProbabilityMeasure Ω₁),
      (klDivBase2 Pxy (Px.prod Qy.toMeasure) = mutual_information Pxy ∧ mutual_information Pxy < ⊤) →
      Qy.toMeasure = Py := by
  sorry
