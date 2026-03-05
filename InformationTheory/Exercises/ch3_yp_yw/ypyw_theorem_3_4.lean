import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.General.ProbabilityProjectionProofs

-- Theorem 3.4 in Information Theory: From Coding to Learning

open InformationQuantities DiscreteInformationQuantities MeasureTheory ProbabilityTheory

variable (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [StandardBorelSpace X]


theorem self_mutual_information (Px : Measure X) [IsProbabilityMeasure Px] :
  let Pxx := Px.map (fun x => (x, x))
  haveI : IsProbabilityMeasure Pxx := by
    exact Measure.isProbabilityMeasure_map (μ := Px) (f := fun x => (x, x)) (by fun_prop)
  mutual_information Pxx =
      (by
        classical
        exact
          (if hX : Countable X then
            (by
              letI : Countable X := hX
              exact discrete_entropy Px.toPMF)
          else ⊤)) :=
by sorry

theorem mutual_information_as_diff_entropies (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] [Countable X] [Nonempty X]:
  mutual_information Pxy + conditional_entropy_general Pxy = discrete_entropy Pxy.fst.toPMF :=
by sorry

theorem mutual_information_as_sum_entropies (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] [Countable X] [Countable Y]:
  mutual_information Pxy + discrete_entropy Pxy.toPMF = discrete_entropy Pxy.fst.toPMF + discrete_entropy Pxy.snd.toPMF :=
by sorry

-- Note: the main issue with this was converting Pxy to the right type via various coercions.
theorem mutual_information_diff_entropy (Pxy : Measure (ℝ × ℝ)) [IsProbabilityMeasure Pxy] :
    let e₂ : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ := by
      simpa [EuclideanSpace] using (MeasurableEquiv.finTwoArrow (α := ℝ))
    let PxyE : Measure (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
      Pxy.map (fun z => (⟨e₂.symm z, Set.mem_univ _⟩ : (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))))
    haveI : IsProbabilityMeasure PxyE :=
      Measure.isProbabilityMeasure_map (μ := Pxy)
        (f := fun z => (⟨e₂.symm z, Set.mem_univ _⟩ : (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))))
        (by
          have hm : Measurable (fun z : ℝ × ℝ => e₂.symm z) := e₂.symm.measurable
          exact (Measurable.subtype_mk hm).aemeasurable)
    (differential_entropy (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) PxyE < ⊤) →
      mutual_information Pxy < ⊤ :=
by
  sorry

theorem mutual_information_bounded_by_entropies (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] [Countable X] [Countable Y] [Nonempty X] [Nonempty Y]:
  let Pyx := Pxy.map Prod.swap
  mutual_information Pxy ≤ min (discrete_entropy Pxy.fst.toPMF) (discrete_entropy Pxy.snd.toPMF)
  ∧ (mutual_information Pxy = min (discrete_entropy Pxy.fst.toPMF) (discrete_entropy Pxy.snd.toPMF))
  -- either H(Y|X) = 0 or H(X|Y) = 0
  ↔ (conditional_entropy_general Pxy = 0 ∨ conditional_entropy_general Pyx = 0)
  -- either X or Y is a det. function of the other
  ↔ ((∃ f : X → Y, ∀ x : X, ∀ y : Y, Pxy.toPMF (x, y) ≠ 0 ↔ f x = y) ∨ (∃ f : Y → X, ∀ x : X, ∀ y : Y, Pxy.toPMF (x, y) ≠ 0 ↔ f y = x)) :=
by sorry
