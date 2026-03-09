import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.ProbabilityProjectionProofs

-- Theorem 4.4 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [StandardBorelSpace Ω] [StandardBorelSpace Ω₁] [Nonempty Ω] [Nonempty Ω₁]
  (Pxy : Measure (Ω × Ω₁)) [IsProbabilityMeasure Pxy]
  (Q_xy : Kernel Ω₁ Ω) [IsMarkovKernel Q_xy]

-- Q_{X|Y=y} ≪ P_X for P_Y a.e. y --> I(X;Y) ≥ E_{P_{X,Y}} [log dQ_{X|Y}/dP_X]
-- and if I(X;Y) < ⊤ then I(X;Y) = sup_{Q_{X|Y}} E_{P_{X,Y}} [log dQ_{X|Y}/dP_X]
theorem sup_characterization_mutual_information :
  let Px : Measure Ω := Pxy.map (fun p : Ω × Ω₁ => p.1)
  let Py : Measure Ω₁ := Pxy.map (fun p : Ω × Ω₁ => p.2)
  (∀ᵐ y ∂Py, (Q_xy y) ≪ Px) →
  ((mutual_information Pxy : EReal) ≥ ((∫ p : Ω × Ω₁,
      Real.log (ENNReal.toReal ((Q_xy p.2).rnDeriv Px p.1))
    ∂Pxy : ℝ) : EReal)
  ∧ (mutual_information Pxy < ⊤ →
  (mutual_information Pxy : EReal) = ⨆ (Q_xy' : Kernel Ω₁ Ω) (_ : IsMarkovKernel Q_xy'),
    ((∫ p : Ω × Ω₁,
        Real.log (ENNReal.toReal ((Q_xy' p.2).rnDeriv Px p.1))
      ∂Pxy : ℝ) : EReal)))
:= by
  sorry
