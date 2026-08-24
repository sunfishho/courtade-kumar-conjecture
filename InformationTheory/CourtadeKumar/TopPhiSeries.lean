import InformationTheory.CourtadeKumar.TopDerivatives
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The absolutely convergent positive power series for the natural-unit
binary entropy defect `topPhi`. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

lemma topPhi_eq_log_formula {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    topPhi x =
      ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2 := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  unfold topPhi
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show 1 - (1 - x) / 2 = (1 + x) / 2 by ring]
  rw [Real.negMulLog_eq_neg]
  change Real.log 2 -
      (-((1 - x) / 2 * Real.log ((1 - x) / 2)) +
        -((1 + x) / 2 * Real.log ((1 + x) / 2))) = _
  rw [Real.log_div hp.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_div hm.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The manuscript series
`topPhi x = ∑ m≥1, x^(2m) / (2m(2m-1))` on the open unit interval.
It is obtained by pairing consecutive terms of two absolutely convergent
logarithm series. -/
theorem topPhi_hasSum {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      x ^ (2 * (n + 1)) /
        (2 * (n + 1) * (2 * (n + 1) - 1))) (topPhi x) := by
  have habs : |x| < 1 := by rw [abs_lt]; exact hx
  let t : ℕ → ℝ := fun n ↦
    -(1 + x) / 2 * ((-x) ^ (n + 1) / (n + 1)) +
      -(1 - x) / 2 * (x ^ (n + 1) / (n + 1))
  have hplus :=
    (Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using habs)).mul_left
      (-(1 + x) / 2)
  have hminus :=
    (Real.hasSum_pow_div_log_of_abs_lt_one (x := x) habs).mul_left
      (-(1 - x) / 2)
  have ht : HasSum t (topPhi x) := by
    have hadd := hplus.add hminus
    convert hadd using 1
    rw [topPhi_eq_log_formula hx]
    simp only [sub_neg_eq_add]
    ring
  have he : Summable (fun n : ℕ ↦ t (2 * n)) :=
    ht.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable (fun n : ℕ ↦ t (2 * n + 1)) :=
    ht.summable.comp_injective (by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      exact Nat.mul_left_cancel (by decide) (Nat.add_right_cancel h))
  have heo :
      tsum (fun n : ℕ ↦ t (2 * n)) + tsum (fun n : ℕ ↦ t (2 * n + 1)) =
        topPhi x := by
    exact (HasSum.even_add_odd he.hasSum ho.hasSum).unique ht
  have hpair := he.hasSum.add ho.hasSum
  rw [heo] at hpair
  convert hpair using 1
  funext n
  dsimp [t]
  rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)),
    Even.neg_pow (⟨n + 1, by omega⟩ : Even (2 * n + 2))]
  push_cast
  have hn : (1 + (n : ℝ) * 2) ≠ 0 := by positivity
  have hscalar :
      ((n : ℝ) * 6 + (n : ℝ) ^ 2 * 4 + 2) *
          (1 + (n : ℝ) * 2)⁻¹ = 2 + (n : ℝ) * 2 := by
    field_simp [hn]
    ring
  have hn2 : (2 + (n : ℝ) * 2) ≠ 0 := by positivity
  have hp : (2 + (n : ℝ) * 6 + (n : ℝ) ^ 2 * 4) ≠ 0 := by positivity
  have hfrac :
      (2 + (n : ℝ) * 6 + (n : ℝ) ^ 2 * 4)⁻¹ =
        (1 + (n : ℝ) * 2)⁻¹ - (2 + (n : ℝ) * 2)⁻¹ := by
    field_simp [hn, hn2, hp]
    ring
  linear_combination (x ^ 2 * x ^ (n * 2)) * hfrac

end CourtadeKumar
