import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.ProbabilityProjectionProofs

-- Theorem 3.2 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory

variable (X Y Z : Type*) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z] [Nonempty X] [Nonempty Y] [Nonempty Z]

theorem mi_as_conditional_kl (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] :
  let product_measure := Pxy.fst.prod Pxy.snd
  mutual_information Pxy = conditionalklDivBase2 Pxy product_measure :=
  by sorry

theorem mi_symmetric (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] :
  let Pyx := Pxy.map Prod.swap
  mutual_information Pxy = mutual_information Pyx :=
  by sorry

theorem mi_positive (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] :
  mutual_information Pxy ≥ 0
  ∧ mutual_information Pxy = 0 ↔ Pxy = Pxy.fst.prod Pxy.snd :=
  by sorry

theorem deterministic_dpi_mi (f : X → Y) (hf : Measurable f) (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] :
  let g : X × Y → Y × Y := fun xy => (f xy.1, xy.2)
  let Pfxy := Pxy.map g
  haveI : IsProbabilityMeasure Pfxy := by
    have hg : Measurable g := (hf.comp measurable_fst).prodMk measurable_snd
    exact Measure.isProbabilityMeasure_map (μ := Pxy) (f := g) hg.aemeasurable
  mutual_information Pxy ≥ mutual_information Pfxy
  -- assume that there exists some function g such that g ∘ f = id, and g is measurable
  -- note that having a left inverse actually already implies injectivity
  ∧ ((∃ g : Y → X, Measurable g ∧ Function.LeftInverse g f) → mutual_information Pxy = mutual_information Pfxy) :=
by sorry


theorem monotonicity_mi (Pxyz : Measure (X × Y × Z)) [IsProbabilityMeasure Pxyz] :
  let Pxz := Pxyz.map (fun p : (X × Y × Z) => (p.1, p.2.2))
  mutual_information Pxyz ≥ mutual_information Pxz :=
by sorry
