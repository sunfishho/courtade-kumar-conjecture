import InformationTheory.CourtadeKumar.TopDerivatives

/-! Monotonicity of the corrected TOP fixed-weight contact residual. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

lemma artanh_neg_eq_neg {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh (-x) = -Real.artanh x := by
  calc
    Real.artanh (-x) = Real.artanh (-Real.tanh (Real.artanh x)) := by
      rw [Real.tanh_artanh hx]
    _ = Real.artanh (Real.tanh (-Real.artanh x)) := by rw [Real.tanh_neg]
    _ = -Real.artanh x := Real.artanh_tanh _

lemma topP_neg {rho x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    topP rho (-x) = -topP rho x := by
  unfold topP
  rw [artanh_neg_eq_neg hx]
  ring

lemma topP_monotoneOn
    (rho : ℝ) (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho) :
    MonotoneOn (topP rho) (Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hartanh := Real.strictMonoOn_artanh.monotoneOn hx hy hxy
  unfold topP
  exact add_le_add
    (mul_le_mul_of_nonneg_left hartanh hs)
    (mul_le_mul_of_nonneg_left hxy (by positivity))

lemma topContactResidual_deriv_nonneg
    {rho c r X : ℝ}
    (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho) (hX : 0 ≤ X)
    (hplus : X + c * r ∈ Ioo (-1 : ℝ) 1)
    (hminus : X - c * r ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ (topP rho (X + c * r) + topP rho (X - c * r)) / 2 := by
  have hneg : -(X - c * r) ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hminus.1, hminus.2]
  have hle : -(X - c * r) ≤ X + c * r := by linarith
  have hmono := topP_monotoneOn rho hs hell hneg hplus hle
  rw [topP_neg hminus] at hmono
  linarith

/-- Under the elementary sign conditions, the fixed-weight contact residual
is monotone in the nonnegative center coordinate. -/
theorem topContactResidual_monotoneOn_nonneg
    {rho c r U : ℝ}
    (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho)
    (hdomain : ∀ X ∈ Icc (0 : ℝ) U,
      X + c * r ∈ Ioo (-1 : ℝ) 1 ∧ X - c * r ∈ Ioo (-1 : ℝ) 1) :
    MonotoneOn (topContactResidual rho c r) (Icc (0 : ℝ) U) := by
  let derivF : ℝ → ℝ := fun X ↦
    (topP rho (X + c * r) + topP rho (X - c * r)) / 2
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 U)
  · intro X hX
    exact (hasDerivAt_topContactResidual (hdomain X hX).1 (hdomain X hX).2).continuousAt.continuousWithinAt
  · intro X hX
    have hXin : X ∈ Icc (0 : ℝ) U := interior_subset hX
    exact (hasDerivAt_topContactResidual (hdomain X hXin).1
      (hdomain X hXin).2).hasDerivWithinAt
  · intro X hX
    have hXin : X ∈ Icc (0 : ℝ) U := interior_subset hX
    exact topContactResidual_deriv_nonneg hs hell hXin.1
      (hdomain X hXin).1 (hdomain X hXin).2

/-- A contact in the admissible interval brackets the fixed-weight residual
between its centered and endpoint values. -/
theorem topContactResidual_bracket_of_contact
    {rho c r X U : ℝ}
    (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    topContactResidual rho c r 0 ≤ 0 ∧
      0 ≤ topContactResidual rho c r U := by
  have hU : 0 ≤ U := hX.1.trans hX.2
  have hmono := topContactResidual_monotoneOn_nonneg hs hell hdomain
  have hleft := hmono (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩) hX hX.1
  have hright := hmono hX (show U ∈ Icc (0 : ℝ) U from ⟨hU, le_rfl⟩) hX.2
  rw [hcontact] at hleft hright
  exact ⟨hleft, hright⟩

/-- Consequently, every admissible fixed-weight contact lies at or before
the balanced root in the sense `G(c,r) ≤ 0`. -/
theorem balancedResidual_nonpos_of_contact
    {rho c r X U : ℝ}
    (hs : 0 ≤ topS rho) (hell : 0 ≤ topEll rho)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    balancedResidual rho c r ≤ 0 := by
  rw [← topContactResidual_zero]
  exact (topContactResidual_bracket_of_contact hs hell hX hdomain hcontact).1

end CourtadeKumar
