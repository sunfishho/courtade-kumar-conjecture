import InformationTheory.CourtadeKumar.LRDeterminantIdealIntervalEvaluator
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Stable slope enclosure for the determinant ideal entropy quotient

The positive-input branch of

`lrDeterminantIdealH t = (1+t) * log (1+t) / t`

has derivative `(t - log (1+t)) / t^2`.  Evaluating that expression by
interval arithmetic is poorly conditioned near zero.  This file instead
proves a cancellation-free enclosure depending only on an upper bound `u`:

`1 / (2 * (1+u)^2) <= H'(t) <= 1/2`, for `0 < t <= u`.

The proof is entirely analytic.  Its only logarithmic input is Mathlib's
kernel theorem bounding the positive odd series for the half-log ratio.
-/

namespace CourtadeKumar

/-- A Padé upper bound for `log (1+t)`, obtained from the one-term positive
odd-series estimate after the exact change of variables `z=t/(t+2)`. -/
lemma lrIdealH_log_one_add_upper
    {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ t - t ^ 2 / (2 * (1 + t)) := by
  let z : ℝ := t / (t + 2)
  have hden : 0 < t + 2 := by linarith
  have hone : 0 < 1 + t := by linarith
  have hzNonnegative : 0 ≤ z := by
    exact div_nonneg ht hden.le
  have hzLtOne : z < 1 := by
    dsimp [z]
    rw [div_lt_one hden]
    linarith
  have hzOneNe : 1 - z ≠ 0 := by linarith
  have hratio : (1 + z) / (1 - z) = 1 + t := by
    dsimp [z] at hzOneNe ⊢
    field_simp [hden.ne', hzOneNe]
    <;> ring
  have hseries :
      (1 / 2 : ℝ) * Real.log (1 + t) ≤
        z + z ^ 3 / (1 - z ^ 2) := by
    simpa [hratio] using
      (Real.log_div_le_sum_range_add hzNonnegative hzLtOne 1)
  have hzProduct : 0 ≤ z * (1 - z) :=
    mul_nonneg hzNonnegative (sub_nonneg.mpr hzLtOne.le)
  have hbase : 0 < 1 - z ^ 2 := by
    nlinarith
  have hpadeIdentity :
      2 * (z + z ^ 3 / (1 - z ^ 2)) =
        t - t ^ 2 / (2 * (1 + t)) := by
    have hcombine :
        z + z ^ 3 / (1 - z ^ 2) = z / (1 - z ^ 2) := by
      field_simp [hbase.ne']
      ring
    rw [hcombine]
    have honeMinus :
        1 - (t / (t + 2)) ^ 2 =
          4 * (1 + t) / (t + 2) ^ 2 := by
      field_simp [hden.ne']
      ring
    dsimp [z]
    rw [honeMinus]
    field_simp [hden.ne', hone.ne']
    ring
  calc
    Real.log (1 + t) ≤
        2 * (z + z ^ 3 / (1 - z ^ 2)) := by
      nlinarith [hseries]
    _ = t - t ^ 2 / (2 * (1 + t)) := hpadeIdentity

/-- The cancellation-free positive-input slope bounds.  The lower estimate
`1/(2*(1+u))` is stronger than the square-denominator estimate needed by the
mean-value evaluator. -/
theorem lrDeterminantIdealH_slope_bounds_strong
    {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 / (2 * (1 + u)) ≤
        (t - Real.log (1 + t)) / t ^ 2 ∧
      (t - Real.log (1 + t)) / t ^ 2 ≤ 1 / 2 := by
  have htOne : 0 < 1 + t := by linarith
  have htTwo : 0 < t + 2 := by linarith
  have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hlogUpper := lrIdealH_log_one_add_upper ht.le
  have hlogLower := Real.le_log_one_add_of_nonneg ht.le
  have hnumLower :
      t ^ 2 / (2 * (1 + t)) ≤ t - Real.log (1 + t) := by
    linarith
  have hsubtractIdentity :
      t - 2 * t / (t + 2) = t ^ 2 / (t + 2) := by
    field_simp [htTwo.ne']
    <;> ring
  have hnumUpper :
      t - Real.log (1 + t) ≤ t ^ 2 / (t + 2) := by
    linarith [hsubtractIdentity]
  constructor
  · have hdenOrder : 2 * (1 + t) ≤ 2 * (1 + u) := by
      linarith
    have hreciprocal :
        1 / (2 * (1 + u)) ≤ 1 / (2 * (1 + t)) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) htOne) hdenOrder
    apply hreciprocal.trans
    rw [le_div_iff₀ htSq]
    calc
      1 / (2 * (1 + t)) * t ^ 2 =
          t ^ 2 / (2 * (1 + t)) := by ring
      _ ≤ t - Real.log (1 + t) := hnumLower
  · rw [div_le_iff₀ htSq]
    have hfrac : t ^ 2 / (t + 2) ≤ t ^ 2 / 2 := by
      rw [div_le_iff₀ htTwo]
      have hcubic : 0 ≤ t ^ 2 * t :=
        mul_nonneg (sq_nonneg t) ht.le
      nlinarith [sq_nonneg t]
    convert hnumUpper.trans hfrac using 1 <;> ring

/-- The square-denominator version used by a uniform slope interval over a
positive box with upper endpoint `u`. -/
theorem lrDeterminantIdealH_slope_bounds
    {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 / (2 * (1 + u) ^ 2) ≤
        (t - Real.log (1 + t)) / t ^ 2 ∧
      (t - Real.log (1 + t)) / t ^ 2 ≤ 1 / 2 := by
  have hstrong := lrDeterminantIdealH_slope_bounds_strong ht htu
  have huNonnegative : 0 ≤ u := ht.le.trans htu
  have huOne : 0 < 1 + u := by linarith
  have hdenOrder :
      2 * (1 + u) ≤ 2 * (1 + u) ^ 2 := by
    nlinarith [sq_nonneg u]
  have hreciprocal :
      1 / (2 * (1 + u) ^ 2) ≤ 1 / (2 * (1 + u)) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) huOne) hdenOrder
  exact ⟨hreciprocal.trans hstrong.1, hstrong.2⟩

/-- The same estimate stated for Lean's derivative of the continuous ideal
entropy quotient. -/
theorem lrDeterminantIdealH_deriv_bounds
    {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 / (2 * (1 + u) ^ 2) ≤ deriv lrDeterminantIdealH t ∧
      deriv lrDeterminantIdealH t ≤ 1 / 2 := by
  rw [(hasDerivAt_lrDeterminantIdealH ht).deriv]
  exact lrDeterminantIdealH_slope_bounds ht htu

/-- A rational slope interval suitable for `IntervalAD.unary`.  It avoids
evaluating `t-log(1+t)` on a narrow positive input interval. -/
def lrDeterminantIdealHSlopeEnclosure
    (input : RationalEnclosure) : RationalEnclosure :=
  ⟨1 / (2 * (1 + input.upper) ^ 2), 1 / 2⟩

theorem lrDeterminantIdealHSlopeEnclosure_contains
    {input : RationalEnclosure} {t : ℝ}
    (hlower : (0 : ℚ) < input.lower)
    (ht : input.Contains t) :
    (lrDeterminantIdealHSlopeEnclosure input).Contains
      ((t - Real.log (1 + t)) / t ^ 2) := by
  have hlowerReal : 0 < (input.lower : ℝ) := by
    exact_mod_cast hlower
  have htPositive : 0 < t := by
    exact hlowerReal.trans_le ht.1
  have hbounds := lrDeterminantIdealH_slope_bounds htPositive ht.2
  simpa [lrDeterminantIdealHSlopeEnclosure,
    RationalEnclosure.Contains] using hbounds

end CourtadeKumar
