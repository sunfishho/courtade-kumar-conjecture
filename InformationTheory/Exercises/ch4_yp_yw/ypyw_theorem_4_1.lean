import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.ProbabilityProjectionProofs

-- Theorem 4.1 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [StandardBorelSpace Ω] [StandardBorelSpace Ω₁] [Nonempty Ω] [Nonempty Ω₁] (Pxy : Measure (Ω × Ω₁)) [IsProbabilityMeasure Pxy]

-- D(P_{Y|X} || Q_Y | P_X) = I(X;Y) + D(P_Y || Q_Y) for any Q_Y
theorem golden_formula (Qy : Measure Ω₁) [IsProbabilityMeasure Qy]:
  let Px : Measure Ω := Pxy.map (fun p : Ω × Ω₁ => p.1)
  let Py : Measure Ω₁ := Pxy.map (fun p : Ω × Ω₁ => p.2)
  (conditionalklDivBase2 (P := Pxy) (Q := Px.prod Qy) = mutual_information Pxy + klDivBase2 Py Qy)
  ∧ (klDivBase2 Py Qy < ⊤ → (mutual_information Pxy = conditionalklDivBase2 (P := Pxy) (Q := Px.prod Qy) - klDivBase2 Py Qy)) :=
by sorry
