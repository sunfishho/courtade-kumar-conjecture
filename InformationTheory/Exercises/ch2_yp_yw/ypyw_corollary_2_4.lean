import Mathlib
import InformationTheory.General.InformationQuantities
import InformationTheory.Discrete.DiscreteInformationQuantities
import InformationTheory.General.Utilities

-- Corollary 2.4 in Information Theory: From Coding to Learning

open MeasureTheory InformationQuantities DiscreteInformationQuantities ENNReal

/-- Needed because we would like ENNReal expectations -/
noncomputable def pmf_expectation {α : Type*} [Countable α] (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, ((p a * (f a)))

theorem cross_entropy_minimum {S : Type*} [Countable S] (P Q : PMF S):
  let cross_entropy := fun (R : PMF S) => pmf_expectation P (fun s : S => (-(Utilities.log2_EReal (R s))).toENNReal)
  (discrete_entropy P < ⊤) → iInf (fun (R : PMF S) => cross_entropy R) = discrete_entropy P ∧ (cross_entropy Q = cross_entropy P → Q = P) := by
  sorry
