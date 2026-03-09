import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.ProbabilityProjectionProofs

-- Theorem 4.3 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [StandardBorelSpace Ω] [StandardBorelSpace Ω₁] [Nonempty Ω] [Nonempty Ω₁] (Pxy : Measure (Ω × Ω₁)) [IsProbabilityMeasure Pxy]

-- I(X;Y) = min_{Q_X, Q_Y} D(P_{X,Y} || Q_X Q_Y)
theorem mutual_information_distance_to_product :
    let Px : Measure Ω := Pxy.map (fun p : Ω × Ω₁ => p.1)
    let Py : Measure Ω₁ := Pxy.map (fun p : Ω × Ω₁ => p.2)
    (mutual_information Pxy = ⨅ (Qx : ProbabilityMeasure Ω) (Qy : ProbabilityMeasure Ω₁),
      klDivBase2 Pxy (Qx.toMeasure.prod Qy.toMeasure)) ∧
    ∀ (Qx : ProbabilityMeasure Ω) (Qy : ProbabilityMeasure Ω₁),
      (klDivBase2 Pxy (Qx.toMeasure.prod Qy.toMeasure) = mutual_information Pxy ∧ mutual_information Pxy < ⊤)→
      Qx.toMeasure = Px ∧ Qy.toMeasure = Py := by
  sorry
