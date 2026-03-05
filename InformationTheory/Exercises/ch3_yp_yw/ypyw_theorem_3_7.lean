import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.General.Utilities
import InformationTheory.General.ProbabilityProjectionProofs

-- Theorem 3.7 in Information Theory: From Coding to Learning

open InformationQuantities MeasureTheory ProbabilityTheory Utilities

variable (X Y Z : Type*) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z] [Nonempty X] [Nonempty Y] [Nonempty Z] (Pxyz : Measure (X × Y × Z)) [IsProbabilityMeasure Pxyz]
variable (W : Type*) [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] (Pxyzw : Measure (X × Y × Z × W)) [IsProbabilityMeasure Pxyzw]

theorem nonneg_conditional_mutual_information :
    conditional_mutual_information Pxyz ≥ 0 ∧ (conditional_mutual_information Pxyz = 0 ↔ isMarkovChain Pxyz) :=
    by sorry

theorem simple_chain_rule :
    -- I(X,Y;Z) = I(X;Z) + I(Y;Z|X)
    mutual_information (Pxyz.map (fun p : X × Y × Z => ((p.1, p.2.1), p.2.2))) =
        mutual_information (Pxyz.map (fun p : X × Y × Z => (p.1, p.2.2))) +
        conditional_mutual_information (Pxyz.map (fun p : X × Y × Z => (p.2.1, p.2.2, p.1)))
    -- I(X,Y;Z) = I(Y;Z) + I(X;Z|Y)
    ∧ mutual_information (Pxyz.map (fun p : X × Y × Z => ((p.1, p.2.1), p.2.2))) =
        mutual_information (Pxyz.map (fun p : X × Y × Z => p.2)) +
        conditional_mutual_information (Pxyz.map (fun p : X × Y × Z => (p.1, p.2.2, p.2.1))) :=
    by sorry

-- X -> Y -> Z implies I(X;Z) ≤ I(X;Y), and equality is equivalent to X <-> Z <-> Y
theorem dpi_mutual_information :
    let Pxz := Pxyz.map (fun p : X × Y × Z => (p.1, p.2.2))
    let Pxy := Pxyz.map (fun p : X × Y × Z => (p.1, p.2.1))
    let Pxzy := Pxyz.map (fun p : X × Y × Z => (p.1, (p.2.2, p.2.1)))
    isMarkovChain Pxyz → (mutual_information Pxz ≤ mutual_information Pxy
    ∧ (mutual_information Pxz = mutual_information Pxy ↔ isMarkovChain Pxzy)) :=
    by sorry

-- X -> Y -> Z -> W implies I(X;W) ≤ I(Y;Z)
theorem markov_chain_mi_inequality :
    letI : IsProbabilityMeasure (Pxyzw.map (fun p : X × Y × Z × W => (p.1, p.2.1, p.2.2.1))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (Pxyzw.map (fun p : X × Y × Z × W => (p.2.1, p.2.2.1, p.2.2.2))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (Pxyzw.map (fun p : X × Y × Z × W => (p.1, p.2.2.2))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (Pxyzw.map (fun p : X × Y × Z × W => (p.2.1, p.2.2.1))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    -- the Markov chain condition is equivalent to breaking this up into two pieces
    isMarkovChain (Pxyzw.map (fun p : X × Y × Z × W => (p.1, p.2.1, p.2.2.1))) →
    isMarkovChain (Pxyzw.map (fun p : X × Y × Z × W => (p.2.1, p.2.2.1, p.2.2.2))) →
    mutual_information (Pxyzw.map (fun p : X × Y × Z × W => (p.1, p.2.2.2))) ≤
    mutual_information (Pxyzw.map (fun p : X × Y × Z × W => (p.2.1, p.2.2.1))) :=
    by sorry

-- General chain rule: I(X^n; Y) = Σ_{k=1}^n I(X_k; Y | X^{k-1})
-- Recursively splits off the last variable: I(X^{n+1}; Y) = I(X^n; Y) + I(X_{n+1}; Y | X^n)
noncomputable def chain_rule_mutual_information_sum :
    ∀ n : ℕ, (α : Fin n → Type*) →
      [∀ i, MeasurableSpace (α i)] → [∀ i, StandardBorelSpace (α i)] → [∀ i, Nonempty (α i)] →
      (β : Type*) → [MeasurableSpace β] → [StandardBorelSpace β] → [Nonempty β] →
      (P : Measure ((∀ i : Fin n, α i) × β)) → [IsProbabilityMeasure P] → ENNReal
  | 0, _, _, _, _, _, _, _, _, _, _ => 0
  | n + 1, α, _, _, hne, β, _, _, _, P, _ =>
      letI : Nonempty (α (Fin.last n)) := hne (Fin.last n)
      letI : IsProbabilityMeasure (P.map fun p : (∀ i : Fin (n+1), α i) × β =>
          (fun (i : Fin n) => p.1 (Fin.castSucc i), p.2)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      letI : IsProbabilityMeasure (P.map fun p : (∀ i : Fin (n+1), α i) × β =>
          (p.1 (Fin.last n), p.2, fun (i : Fin n) => p.1 (Fin.castSucc i))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      chain_rule_mutual_information_sum n (fun i => α (Fin.castSucc i)) β
          (P.map fun p => (fun (i : Fin n) => p.1 (Fin.castSucc i), p.2))
        + conditional_mutual_information
            (P.map fun p => (p.1 (Fin.last n), p.2, fun (i : Fin n) => p.1 (Fin.castSucc i)))

theorem chain_rule_mutual_information_full
    (n : ℕ+) (α : Fin n → Type*)
    [∀ i, MeasurableSpace (α i)] [∀ i, StandardBorelSpace (α i)] [∀ i, Nonempty (α i)]
    (β : Type*) [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    (P : Measure ((∀ i : Fin n, α i) × β)) [IsProbabilityMeasure P] :
    mutual_information P = chain_rule_mutual_information_sum n α β P := by
  sorry

-- I(f(X); g(Y)) = I(X; Y) when f, g are one to one with measurable inverses
-- We note that the existence of a measurable inverse imply f, g are one to one
theorem permutation_invariance_mutual_information
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [StandardBorelSpace S] [StandardBorelSpace T]
    (f : X → S) (hf : Measurable f) (hf_inv : ∃ f' : S → X, Measurable f' ∧ Function.LeftInverse f' f)
    (g : Y → T) (hg : Measurable g) (hg_inv : ∃ g' : T → Y, Measurable g' ∧ Function.LeftInverse g' g)
    (Pxy : Measure (X × Y)) [IsProbabilityMeasure Pxy] :
    letI : IsProbabilityMeasure (Pxy.map (fun p : X × Y => (f p.1, g p.2))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    mutual_information (Pxy.map (fun p : X × Y => (f p.1, g p.2))) = mutual_information Pxy :=
    by sorry
