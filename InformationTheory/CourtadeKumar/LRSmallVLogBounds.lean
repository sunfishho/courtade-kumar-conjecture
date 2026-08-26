import InformationTheory.CourtadeKumar.LRSmallVZeroFactor

/-!
# Exact logarithmic bound for the small-odds tail

The estimate `(8/3) log 2 - log 3 < 3/4` is proved through the equivalent
integer inequality `256/27 < exp(9/4)`.  The exponential lower bound uses
only `exp(1) > 2.7182818283` and `(1+x)^n ≤ exp(nx)`.
-/

namespace CourtadeKumar

theorem lr_exp_nine_fourths_gt :
    (256 / 27 : ℝ) < Real.exp (9 / 4) := by
  let e₀ : ℝ := 27182818283 / 10000000000
  let q₀ : ℝ := 401 / 400
  have he : e₀ < Real.exp 1 := by
    dsimp [e₀]
    convert Real.exp_one_gt_d9 using 1 <;> norm_num
  have he0 : 0 ≤ e₀ := by norm_num [e₀]
  have heSq : e₀ ^ 2 < (Real.exp 1) ^ 2 :=
    pow_lt_pow_left₀ he he0 (by norm_num)
  have hbase : q₀ ≤ Real.exp (1 / 400 : ℝ) := by
    dsimp [q₀]
    nlinarith [Real.add_one_le_exp (1 / 400 : ℝ)]
  have hq0 : 0 ≤ q₀ := by norm_num [q₀]
  have hpow := pow_le_pow_left₀ hq0 hbase 100
  have hquarter : q₀ ^ 100 ≤ Real.exp (1 / 4 : ℝ) := by
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    exact hpow
  have hqPowPos : 0 < q₀ ^ 100 := by positivity
  have hfirst : e₀ ^ 2 * q₀ ^ 100 <
      (Real.exp 1) ^ 2 * q₀ ^ 100 :=
    mul_lt_mul_of_pos_right heSq hqPowPos
  have hsecond : (Real.exp 1) ^ 2 * q₀ ^ 100 ≤
      (Real.exp 1) ^ 2 * Real.exp (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left hquarter (sq_nonneg _)
  have hrational : (256 / 27 : ℝ) < e₀ ^ 2 * q₀ ^ 100 := by
    norm_num [e₀, q₀]
  calc
    (256 / 27 : ℝ) < e₀ ^ 2 * q₀ ^ 100 := hrational
    _ < (Real.exp 1) ^ 2 * q₀ ^ 100 := hfirst
    _ ≤ (Real.exp 1) ^ 2 * Real.exp (1 / 4 : ℝ) := hsecond
    _ = Real.exp (9 / 4) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      norm_num

theorem lr_smallV_terminal_log_bound :
    (8 / 3 : ℝ) * Real.log 2 - Real.log 3 < 3 / 4 := by
  have hlog : Real.log (256 / 27 : ℝ) < 9 / 4 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 lr_exp_nine_fourths_gt
  have hid : Real.log (256 / 27 : ℝ) =
      8 * Real.log 2 - 3 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (256 : ℝ) = 2 ^ 8 by norm_num,
      show (27 : ℝ) = 3 ^ 3 by norm_num,
      Real.log_pow, Real.log_pow]
    norm_num
  rw [hid] at hlog
  linarith

end CourtadeKumar
