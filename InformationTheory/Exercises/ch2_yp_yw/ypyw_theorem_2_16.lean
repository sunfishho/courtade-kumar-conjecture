import Mathlib
import InformationTheory.General.InformationQuantities

-- Theorem 2.16 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [StandardBorelSpace X]

theorem conditional_kl_as_unconditional (P : Measure X) [IsProbabilityMeasure P] (Pyx : Kernel X Y) [IsMarkovKernel Pyx] (Qyx : Kernel X Y) [Nonempty Y][IsMarkovKernel Qyx] :
  let Pjoint := P.compProd Pyx
  let Qjoint := P.compProd Qyx
  conditionalklDivBase2 Pjoint Qjoint = klDivBase2 Pjoint Qjoint := by
  sorry

theorem monotonic_kl_divergence (Pxy : Measure (X × Y)) (Qxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] [IsProbabilityMeasure Qxy] :
  let Px := Pxy.fst
  let Qx := Qxy.fst
  klDivBase2 Pxy Qxy ≥ klDivBase2 Px Qx := by
  sorry


noncomputable def chain_rule_kl_sum :
    ∀ n : ℕ, (α : Fin n → Type*) →
      [∀ i, MeasurableSpace (α i)] → [∀ i, StandardBorelSpace (α i)] → [∀ i, Nonempty (α i)] →
      (P Q : Measure (∀ i : Fin n, α i)) → [IsProbabilityMeasure P] → [IsProbabilityMeasure Q] → ℝ≥0∞
  | 0, _, _, _, _, _, _, _, _ => 0
  | n + 1, α, _, _, _, P, Q, _, _ =>
      let toPair : (∀ i : Fin (n+1), α i) → (∀ i : Fin n, α (Fin.castSucc i)) × α (Fin.last n) :=
        fun x => (fun (i : Fin n) => x (Fin.castSucc i), x (Fin.last n))
      letI : IsProbabilityMeasure (P.map toPair) := Measure.isProbabilityMeasure_map (by fun_prop)
      letI : IsProbabilityMeasure (Q.map toPair) := Measure.isProbabilityMeasure_map (by fun_prop)
      chain_rule_kl_sum n (fun i => α (Fin.castSucc i)) (P.map toPair).fst (Q.map toPair).fst
        + conditionalklDivBase2 (P.map toPair) (Q.map toPair)

theorem full_kl_chain_rule
    (n : ℕ) (α : Fin n → Type*)
    [∀ i, MeasurableSpace (α i)] [∀ i, StandardBorelSpace (α i)] [∀ i, Nonempty (α i)]
    (P Q : Measure (∀ i : Fin n, α i)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDivBase2 P Q = chain_rule_kl_sum n α P Q := by
  sorry

theorem tensorization_kl
    (n : ℕ)
    (α : Fin n → Type*)
    [∀ i : Fin n, MeasurableSpace (α i)]
    [∀ i : Fin n, StandardBorelSpace (α i)]
    [∀ i : Fin n, Nonempty (α i)]
    (P : ∀ i : Fin n, Measure (α i))
    (Q : ∀ i : Fin n, Measure (α i))
    [∀ i : Fin n, IsProbabilityMeasure (P i)]
    [∀ i : Fin n, IsProbabilityMeasure (Q i)] :
    let Pjoint : Measure (∀ i : Fin n, α i) := Measure.pi P
    let Qjoint : Measure (∀ i : Fin n, α i) := Measure.pi Q
    ∑ i : Fin n, klDivBase2 (P i) (Q i) = klDivBase2 Pjoint Qjoint := by
  sorry

theorem conditioning_increases_divergence
  (Px : Measure X)
  [IsProbabilityMeasure Px]
  (Pyx : Kernel X Y)
  [IsMarkovKernel Pyx]
  (Qyx : Kernel X Y)
  [IsMarkovKernel Qyx]
  [Nonempty X]
  [Nonempty Y] :
  let Py := Px.bind Pyx
  let Qy := Px.bind Qyx
  let Pxy := Pyx † Px
  let Qxy := Qyx † Px
  klDivBase2 Py Qy ≤ conditionalklDivBase2 (Px.compProd Pyx) (Px.compProd Qyx)
  ∧ klDivBase2 Py Qy = conditionalklDivBase2 (Px.compProd Pyx) (Px.compProd Qyx) ↔ conditionalklDivBase2 (Py.compProd Pxy) (Py.compProd Qxy) = 0 := by
sorry
