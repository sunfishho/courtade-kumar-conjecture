import Mathlib
import InformationTheory.Discrete.DiscreteInformationQuantities

-- Theorem 1.4 in Information Theory: From Coding to Learning

open DiscreteInformationQuantities MeasureTheory ProbabilityTheory ENNReal

variable {S T : Type*}
  [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [Nonempty S]
  [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T] [Nonempty T]

/-- entropy is positive -/
theorem entropy_positivity (x_pmf : PMF S) : discrete_entropy x_pmf ≥ 0 := by
  sorry

/-- entropy is zero if and only if the random variable is deterministic -/
theorem entropy_zero (x_pmf : PMF S) :
    discrete_entropy x_pmf = 0 ↔ ∃ s : S, x_pmf s = 1 := by
  sorry

/-- entropy is maximized by the uniform distribution -/
theorem entropy_max (x_pmf : PMF S) [Fintype S] :
    discrete_entropy x_pmf ≤ discrete_entropy (PMF.uniformOfFintype S) := by
  sorry

/-- entropy is invariant under bijections -/
theorem entropy_under_bij_f (x_pmf : PMF S) [Fintype S] [Fintype T] (f: S → T) (hf: Function.Bijective f) :
discrete_entropy x_pmf = discrete_entropy (PMF.map f x_pmf):= by
sorry

/--H(X) ≥ H(X|Y) -/
theorem conditioning_reduces_entropy (joint_pmf : PMF (S × T)) :
  let x_pmf : PMF S := PMF.map Prod.fst joint_pmf
  discrete_entropy x_pmf ≥ discrete_conditional_entropy joint_pmf := by
  sorry

/-- chain rule for entropy: H(X,Y) = H(X) + H(Y|X) -/
theorem chain_rule_entropy (joint_pmf : PMF (S × T)) :
  let x_pmf : PMF S := PMF.map Prod.fst joint_pmf
  discrete_entropy joint_pmf = discrete_entropy (x_pmf) + discrete_conditional_entropy (joint_pmf.map Prod.swap) := by
  sorry

-- note: statement in book was incorrect, we require a finiteness assumption on S. as a counterexample, consider a PMF that has infinite entropy over the natural numbers, and some not one-to-one function which takes this to another PMF with infinite entropy.
/-- entropy can only decrease under deterministic transformations. One-to-one case is equality -/
theorem entropy_under_det_transform (x_pmf : PMF S) [Fintype S] [Fintype T] (f: S → T) :
  discrete_entropy x_pmf ≥ discrete_entropy (PMF.map f x_pmf) ∧ (Finite S → (discrete_entropy x_pmf = discrete_entropy (PMF.map f x_pmf) ↔ Set.InjOn f (x_pmf.support : Set S))) := by
sorry

/-- A recursive “chain rule sum” built from conditional entropies by splitting off the last coordinate. -/
noncomputable def chain_rule_entropy_sum :
    ∀ n : ℕ, (α : Fin n → Type*) → (∀ i : Fin n, Countable (α i)) → PMF (∀ i : Fin n, α i) → ℝ≥0∞
  | 0, _, _, _ => 0
  | n + 1, α, hα, joint_pmf =>
      letI : Countable (α (Fin.last n)) := hα (Fin.last n)
      letI : ∀ i : Fin n, Countable (α (Fin.castSucc i)) := fun i => hα (Fin.castSucc i)
      let pair_pmf := PMF.map (Fin.snocEquiv α).symm joint_pmf
      chain_rule_entropy_sum n (fun i => α (Fin.castSucc i)) (fun i => hα (Fin.castSucc i))
          (PMF.map Prod.snd pair_pmf)
        + discrete_conditional_entropy pair_pmf

/-- Chain rule for any number of random variables, subadditivity, and equality implying independence of PMFs -/
theorem chain_rule_entropy_full {n : ℕ+} (α : Fin n → Type*) [∀ i : Fin n, Countable (α i)] (joint_pmf : PMF (∀ i : Fin n, α i)) :
    discrete_entropy joint_pmf =
        chain_rule_entropy_sum (n := (n : ℕ)) α (fun i => (by infer_instance : Countable (α i)))
          joint_pmf ∧
      discrete_entropy joint_pmf ≤ ∑ i : Fin n, discrete_entropy (PMF.map (fun x => x i) joint_pmf) ∧
      (discrete_entropy joint_pmf =
          ∑ i : Fin n, discrete_entropy (PMF.map (fun x => x i) joint_pmf)) →
        ∀ x : (∀ i : Fin n, α i),
          joint_pmf x = ∏ i : Fin n, (PMF.map (fun y => y i) joint_pmf) (x i) := by
  sorry
