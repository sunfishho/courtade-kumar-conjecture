import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lightweight natural binary-entropy scalars

This module contains only the scalar definitions shared by the analytic TOP
development and the exact `Q/Q'` point certificates.  Keeping them independent
of the historical envelope and channel chain lets semantic point promotion use
the same functions without loading the full TOP proof stack.
-/

namespace CourtadeKumar

noncomputable def topPhi (x : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy ((1 - x) / 2)

@[simp] lemma topPhi_one : topPhi 1 = Real.log 2 := by simp [topPhi]

@[simp] lemma topPhi_neg_one : topPhi (-1) = Real.log 2 := by simp [topPhi]

@[simp] lemma topPhi_zero : topPhi 0 = 0 := by
  rw [topPhi, show ((1 - (0 : ℝ)) / 2) = (2 : ℝ)⁻¹ by norm_num,
    Real.binEntropy_two_inv]
  ring

noncomputable def topJ (x : ℝ) : ℝ := Real.log 2 - topPhi x

@[simp] lemma topJ_neg (x : ℝ) : topJ (-x) = topJ x := by
  unfold topJ topPhi
  rw [show (1 - -x) / 2 = 1 - (1 - x) / 2 by ring,
    Real.binEntropy_one_sub]

lemma topJ_eq_binEntropy (x : ℝ) :
    topJ x = Real.binEntropy ((1 - x) / 2) := by
  unfold topJ topPhi
  ring

end CourtadeKumar
