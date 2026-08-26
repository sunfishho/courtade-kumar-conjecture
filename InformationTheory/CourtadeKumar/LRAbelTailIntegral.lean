import InformationTheory.CourtadeKumar.LRAbelPrefixEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integral representation of the positive tail `log 2 - Φ_N(1)`. -/

open Set
open scoped Interval

namespace CourtadeKumar

noncomputable def lrAbelTailIntegral (N : ℕ) : ℝ :=
  ∫ y : ℝ in 0..1, y ^ (2 * N) / (1 + y)

lemma lrAbelTailIntegral_zero :
    lrAbelTailIntegral 0 = Real.log 2 := by
  unfold lrAbelTailIntegral
  simp only [Nat.mul_zero, pow_zero, one_div]
  calc
    (∫ y : ℝ in 0..1, (1 + y)⁻¹) =
        ∫ x : ℝ in 1..2, x⁻¹ := by
      have hadd : (fun y : ℝ ↦ (1 + y)⁻¹) = (fun y : ℝ ↦ (y + 1)⁻¹) := by
        funext y
        rw [add_comm]
      rw [hadd]
      convert (intervalIntegral.integral_comp_add_right (fun x : ℝ ↦ x⁻¹) 1
        (a := 0) (b := 1)) using 1
      all_goals norm_num
    _ = Real.log (2 / 1) := integral_inv_of_pos (by norm_num) (by norm_num)
    _ = Real.log 2 := by norm_num

lemma lrAbelTailValue_zero :
    lrAbelTailValue 0 = Real.log 2 := by
  simp [lrAbelTailValue, lrAbelPhiPrefixAtOne]

lemma lrAbelPhiPrefixAtOne_succ (N : ℕ) :
    lrAbelPhiPrefixAtOne (N + 1) =
      lrAbelPhiPrefixAtOne N +
        1 / ((2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) := by
  unfold lrAbelPhiPrefixAtOne
  rw [Finset.sum_range_succ]
  congr 1
  ring

lemma lrAbelTailValue_succ (N : ℕ) :
    lrAbelTailValue (N + 1) =
      lrAbelTailValue N -
        1 / ((2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) := by
  unfold lrAbelTailValue
  rw [lrAbelPhiPrefixAtOne_succ]
  ring

lemma lrAbelTailIntegrand_intervalIntegrable (N : ℕ) :
    IntervalIntegrable (fun y : ℝ ↦ y ^ (2 * N) / (1 + y))
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · exact continuous_pow (2 * N) |>.continuousOn
  · exact (continuous_const.add continuous_id).continuousOn
  · intro y hy
    have hy0 : 0 ≤ y := by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy.1
    linarith

lemma lrAbelTailIntegral_sub_succ (N : ℕ) :
    lrAbelTailIntegral N - lrAbelTailIntegral (N + 1) =
      1 / ((2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) := by
  unfold lrAbelTailIntegral
  rw [← intervalIntegral.integral_sub
    (lrAbelTailIntegrand_intervalIntegrable N)
    (lrAbelTailIntegrand_intervalIntegrable (N + 1))]
  have hpoint : ∀ y ∈ uIcc (0 : ℝ) 1,
      y ^ (2 * N) / (1 + y) - y ^ (2 * (N + 1)) / (1 + y) =
        y ^ (2 * N) - y ^ (2 * N + 1) := by
    intro y hy
    have hy0 : 0 ≤ y := by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy.1
    have hden : 1 + y ≠ 0 := by linarith
    have hpow1 : y ^ (2 * N + 1) = y ^ (2 * N) * y := by rw [pow_succ]
    have hpow2 : y ^ (2 * (N + 1)) = y ^ (2 * N) * y ^ 2 := by
      rw [show 2 * (N + 1) = 2 * N + 2 by omega, pow_add]
    rw [hpow1, hpow2]
    field_simp [hden]
    ring
  rw [intervalIntegral.integral_congr hpoint]
  rw [intervalIntegral.integral_sub
    (continuous_pow (2 * N) |>.intervalIntegrable 0 1)
    (continuous_pow (2 * N + 1) |>.intervalIntegrable 0 1)]
  rw [integral_pow, integral_pow]
  norm_num only [one_pow, zero_pow, Nat.succ_ne_zero, sub_zero]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

theorem lrAbelTailValue_eq_integral (N : ℕ) :
    lrAbelTailValue N = lrAbelTailIntegral N := by
  induction N with
  | zero => rw [lrAbelTailValue_zero, lrAbelTailIntegral_zero]
  | succ N ih =>
      rw [lrAbelTailValue_succ, ih]
      have hrec := lrAbelTailIntegral_sub_succ N
      linarith

end CourtadeKumar
