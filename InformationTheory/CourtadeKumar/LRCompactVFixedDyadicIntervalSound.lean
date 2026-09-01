import InformationTheory.CourtadeKumar.LRCompactVFixedDyadicIntervalCore
import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Soundness of compact-V fixed-dyadic interval arithmetic

This file is the semantic half of `LRCompactVFixedDyadicIntervalCore`.
The executable layer stores only integer numerators.  Here those numerators
are decoded, the four directed-rounding branches are justified, and the
small bundled operations needed by a linear-time Taylor-jet evaluator are
proved to preserve real containment.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVFixedDyadic

theorem scale_pos (bits : ℕ) : 0 < scale bits := by
  simp [scale]

theorem scale_rat_pos (bits : ℕ) : (0 : ℚ) < (scale bits : ℚ) := by
  exact_mod_cast scale_pos bits

theorem scale_real_pos (bits : ℕ) : (0 : ℝ) < (scale bits : ℝ) := by
  exact_mod_cast scale_pos bits

theorem decodeNat_nonnegative (bits value : ℕ) :
    (0 : ℚ) ≤ decodeNat bits value := by
  exact div_nonneg (by positivity) (le_of_lt (scale_rat_pos bits))

theorem decodeNat_real_nonnegative (bits value : ℕ) :
    (0 : ℝ) ≤ (decodeNat bits value : ℝ) := by
  exact_mod_cast decodeNat_nonnegative bits value

theorem decodeInt_real_nonnegative_of_nonnegative
    (bits : ℕ) {value : ℤ} (hvalue : 0 ≤ value) :
    (0 : ℝ) ≤ (decodeInt bits value : ℝ) := by
  have hq : (0 : ℚ) ≤ decodeInt bits value := by
    exact div_nonneg (by exact_mod_cast hvalue) (le_of_lt (scale_rat_pos bits))
  exact_mod_cast hq

theorem decodeInt_real_nonpositive_of_nonpositive
    (bits : ℕ) {value : ℤ} (hvalue : value ≤ 0) :
    (decodeInt bits value : ℝ) ≤ 0 := by
  have hq : decodeInt bits value ≤ (0 : ℚ) := by
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hvalue)
      (le_of_lt (scale_rat_pos bits))
  exact_mod_cast hq

@[simp] theorem decodeNat_add (bits left right : ℕ) :
    decodeNat bits (left + right) =
      decodeNat bits left + decodeNat bits right := by
  simp [decodeNat]
  ring

@[simp] theorem decodeNat_scaleNat (bits coefficient value : ℕ) :
    decodeNat bits (coefficient * value) =
      (coefficient : ℚ) * decodeNat bits value := by
  simp [decodeNat]
  ring

@[simp] theorem decodeInt_add (bits : ℕ) (left right : ℤ) :
    decodeInt bits (left + right) =
      decodeInt bits left + decodeInt bits right := by
  simp [decodeInt]
  ring

@[simp] theorem decodeInt_neg (bits : ℕ) (value : ℤ) :
    decodeInt bits (-value) = -decodeInt bits value := by
  simp [decodeInt]
  ring

@[simp] theorem decodeInt_scaleNat
    (bits coefficient : ℕ) (value : ℤ) :
    decodeInt bits ((coefficient : ℤ) * value) =
      (coefficient : ℚ) * decodeInt bits value := by
  simp [decodeInt]
  ring

theorem decodeNat_add_real (bits left right : ℕ) :
    (decodeNat bits (left + right) : ℝ) =
      (decodeNat bits left : ℝ) + (decodeNat bits right : ℝ) := by
  exact_mod_cast decodeNat_add bits left right

theorem decodeNat_scaleNat_real (bits coefficient value : ℕ) :
    (decodeNat bits (coefficient * value) : ℝ) =
      (coefficient : ℝ) * (decodeNat bits value : ℝ) := by
  exact_mod_cast decodeNat_scaleNat bits coefficient value

theorem decodeInt_add_real (bits : ℕ) (left right : ℤ) :
    (decodeInt bits (left + right) : ℝ) =
      (decodeInt bits left : ℝ) + (decodeInt bits right : ℝ) := by
  exact_mod_cast decodeInt_add bits left right

theorem decodeInt_neg_real (bits : ℕ) (value : ℤ) :
    (decodeInt bits (-value) : ℝ) = -(decodeInt bits value : ℝ) := by
  exact_mod_cast decodeInt_neg bits value

theorem decodeInt_scaleNat_real
    (bits coefficient : ℕ) (value : ℤ) :
    (decodeInt bits ((coefficient : ℤ) * value) : ℝ) =
      (coefficient : ℝ) * (decodeInt bits value : ℝ) := by
  exact_mod_cast decodeInt_scaleNat bits coefficient value

@[simp] theorem decodeInt_natCast (bits value : ℕ) :
    decodeInt bits (value : ℤ) = decodeNat bits value := by
  simp [decodeInt, decodeNat]

@[simp] theorem decodeInt_neg_natCast (bits value : ℕ) :
    decodeInt bits (-((value : ℕ) : ℤ)) = -decodeNat bits value := by
  simp [decodeInt, decodeNat]
  ring

theorem decodeInt_eq_decodeNat_toNat_of_nonneg
    (bits : ℕ) {value : ℤ} (hvalue : 0 ≤ value) :
    decodeInt bits value = decodeNat bits value.toNat := by
  rw [← decodeInt_natCast]
  congr
  exact (Int.toNat_of_nonneg hvalue).symm

theorem decodeInt_eq_neg_decodeNat_toNat_neg_of_nonpos
    (bits : ℕ) {value : ℤ} (hvalue : value ≤ 0) :
    decodeInt bits value = -decodeNat bits (-value).toNat := by
  rw [← decodeInt_neg_natCast]
  congr
  have hneg : 0 ≤ -value := neg_nonneg.mpr hvalue
  simpa using congrArg Neg.neg (Int.toNat_of_nonneg hneg).symm

theorem mulDown_eq_div (bits left right : ℕ) :
    mulDown bits left right = left * right / scale bits := by
  simpa only [mulDown, scale] using
    Nat.shiftRight_eq_div_pow (left * right) bits

theorem mulUp_eq_ceilDiv (bits left right : ℕ) :
    mulUp bits left right = ceilDiv (left * right) (scale bits) := by
  simpa only [mulUp, ceilDiv, scale] using
    Nat.shiftRight_eq_div_pow (left * right + 2 ^ bits - 1) bits

theorem div_mul_le (value divisor : ℕ) :
    value / divisor * divisor ≤ value :=
  Nat.div_mul_le_self value divisor

theorem le_ceilDiv_mul {value divisor : ℕ} (hdivisor : 0 < divisor) :
    value ≤ ceilDiv value divisor * divisor := by
  have h :=
    (ceilDiv_le_iff_le_mul hdivisor :
      value ⌈/⌉ divisor ≤ value ⌈/⌉ divisor ↔
        value ≤ divisor * (value ⌈/⌉ divisor)).mp le_rfl
  simpa [ceilDiv, Nat.ceilDiv_eq_add_pred_div, mul_comm] using h

theorem mulDown_mul_scale_le (bits left right : ℕ) :
    mulDown bits left right * scale bits ≤ left * right := by
  rw [mulDown_eq_div]
  exact div_mul_le _ _

theorem le_mulUp_mul_scale (bits left right : ℕ) :
    left * right ≤ mulUp bits left right * scale bits := by
  rw [mulUp_eq_ceilDiv]
  exact le_ceilDiv_mul (scale_pos bits)

theorem decodeNat_mulDown_le (bits left right : ℕ) :
    decodeNat bits (mulDown bits left right) ≤
      decodeNat bits left * decodeNat bits right := by
  have hs := scale_rat_pos bits
  have hnum :
      ((mulDown bits left right * scale bits : ℕ) : ℚ) ≤
        ((left * right : ℕ) : ℚ) := by
    exact_mod_cast mulDown_mul_scale_le bits left right
  unfold decodeNat
  calc
    (mulDown bits left right : ℚ) / (scale bits : ℚ) =
        ((mulDown bits left right * scale bits : ℕ) : ℚ) /
          ((scale bits : ℚ) * (scale bits : ℚ)) := by
            norm_num
            field_simp [ne_of_gt hs]
    _ ≤ ((left * right : ℕ) : ℚ) /
          ((scale bits : ℚ) * (scale bits : ℚ)) := by
            exact (div_le_div_iff_of_pos_right (mul_pos hs hs)).2 hnum
    _ = ((left : ℚ) / (scale bits : ℚ)) *
          ((right : ℚ) / (scale bits : ℚ)) := by
            norm_num
            field_simp [ne_of_gt hs]

theorem decodeNat_le_mulUp (bits left right : ℕ) :
    decodeNat bits left * decodeNat bits right ≤
      decodeNat bits (mulUp bits left right) := by
  have hs := scale_rat_pos bits
  have hnum :
      ((left * right : ℕ) : ℚ) ≤
        ((mulUp bits left right * scale bits : ℕ) : ℚ) := by
    exact_mod_cast le_mulUp_mul_scale bits left right
  unfold decodeNat
  calc
    ((left : ℚ) / (scale bits : ℚ)) *
          ((right : ℚ) / (scale bits : ℚ)) =
        ((left * right : ℕ) : ℚ) /
          ((scale bits : ℚ) * (scale bits : ℚ)) := by
            norm_num
            field_simp [ne_of_gt hs]
    _ ≤ ((mulUp bits left right * scale bits : ℕ) : ℚ) /
          ((scale bits : ℚ) * (scale bits : ℚ)) := by
            exact (div_le_div_iff_of_pos_right (mul_pos hs hs)).2 hnum
    _ = (mulUp bits left right : ℚ) / (scale bits : ℚ) := by
          norm_num
          field_simp [ne_of_gt hs]

theorem decodeInt_signedMulDown_le (bits : ℕ)
    (signed : ℤ) (nonnegative : ℕ) :
    decodeInt bits (signedMulDown bits signed nonnegative) ≤
      decodeInt bits signed * decodeNat bits nonnegative := by
  by_cases hsigned : 0 ≤ signed
  · have h := decodeNat_mulDown_le bits signed.toNat nonnegative
    simpa [signedMulDown, hsigned,
      decodeInt_eq_decodeNat_toNat_of_nonneg bits hsigned] using h
  · have hsigned' : signed ≤ 0 := le_of_not_ge hsigned
    have h := neg_le_neg (decodeNat_le_mulUp bits (-signed).toNat nonnegative)
    simpa [signedMulDown, hsigned,
      decodeInt_eq_neg_decodeNat_toNat_neg_of_nonpos bits hsigned'] using h

theorem decodeInt_le_signedMulUp (bits : ℕ)
    (signed : ℤ) (nonnegative : ℕ) :
    decodeInt bits signed * decodeNat bits nonnegative ≤
      decodeInt bits (signedMulUp bits signed nonnegative) := by
  by_cases hsigned : 0 ≤ signed
  · have h := decodeNat_le_mulUp bits signed.toNat nonnegative
    simpa [signedMulUp, hsigned,
      decodeInt_eq_decodeNat_toNat_of_nonneg bits hsigned] using h
  · have hsigned' : signed ≤ 0 := le_of_not_ge hsigned
    have h := neg_le_neg (decodeNat_mulDown_le bits (-signed).toNat nonnegative)
    simpa [signedMulUp, hsigned,
      decodeInt_eq_neg_decodeNat_toNat_neg_of_nonpos bits hsigned'] using h

theorem decodeNat_div_le (bits value divisor : ℕ) (hdivisor : 0 < divisor) :
    decodeNat bits (value / divisor) ≤ decodeNat bits value / divisor := by
  have hs := scale_rat_pos bits
  have hd : (0 : ℚ) < (divisor : ℚ) := by exact_mod_cast hdivisor
  apply (le_div_iff₀ hd).2
  unfold decodeNat
  calc
    ((value / divisor : ℕ) : ℚ) / (scale bits : ℚ) * (divisor : ℚ) =
        (((value / divisor) * divisor : ℕ) : ℚ) /
          (scale bits : ℚ) := by norm_num; ring
    _ ≤ (value : ℚ) / (scale bits : ℚ) := by
      apply (div_le_div_iff_of_pos_right hs).2
      exact_mod_cast div_mul_le value divisor

theorem decodeNat_le_ceilDiv (bits value divisor : ℕ) (hdivisor : 0 < divisor) :
    decodeNat bits value / divisor ≤ decodeNat bits (ceilDiv value divisor) := by
  have hs := scale_rat_pos bits
  have hd : (0 : ℚ) < (divisor : ℚ) := by exact_mod_cast hdivisor
  apply (div_le_iff₀ hd).2
  unfold decodeNat
  calc
    (value : ℚ) / (scale bits : ℚ) ≤
        ((ceilDiv value divisor * divisor : ℕ) : ℚ) /
          (scale bits : ℚ) := by
      apply (div_le_div_iff_of_pos_right hs).2
      exact_mod_cast le_ceilDiv_mul hdivisor
    _ = (ceilDiv value divisor : ℚ) / (scale bits : ℚ) *
          (divisor : ℚ) := by norm_num; ring

theorem decodeInt_signedDivDown_le (bits : ℕ)
    (value : ℤ) (divisor : ℕ) (hdivisor : 0 < divisor) :
    decodeInt bits (signedDivDown value divisor) ≤
      decodeInt bits value / divisor := by
  by_cases hvalue : 0 ≤ value
  · have h := decodeNat_div_le bits value.toNat divisor hdivisor
    have heq : signedDivDown value divisor =
        ((value.toNat / divisor : ℕ) : ℤ) := by
      simp only [signedDivDown, if_pos hvalue]
    rw [heq, decodeInt_natCast,
      decodeInt_eq_decodeNat_toNat_of_nonneg bits hvalue]
    exact h
  · have hvalue' : value ≤ 0 := le_of_not_ge hvalue
    have h := neg_le_neg (decodeNat_le_ceilDiv bits (-value).toNat divisor hdivisor)
    have heq : signedDivDown value divisor =
        -((ceilDiv (-value).toNat divisor : ℕ) : ℤ) := by
      simp only [signedDivDown, if_neg hvalue]
    rw [heq, decodeInt_neg_natCast,
      decodeInt_eq_neg_decodeNat_toNat_neg_of_nonpos bits hvalue']
    simpa only [neg_div] using h

theorem decodeInt_le_signedDivUp (bits : ℕ)
    (value : ℤ) (divisor : ℕ) (hdivisor : 0 < divisor) :
    decodeInt bits value / divisor ≤
      decodeInt bits (signedDivUp value divisor) := by
  by_cases hvalue : 0 ≤ value
  · have h := decodeNat_le_ceilDiv bits value.toNat divisor hdivisor
    have heq : signedDivUp value divisor =
        ((ceilDiv value.toNat divisor : ℕ) : ℤ) := by
      simp only [signedDivUp, if_pos hvalue]
    rw [heq, decodeInt_natCast,
      decodeInt_eq_decodeNat_toNat_of_nonneg bits hvalue]
    exact h
  · have hvalue' : value ≤ 0 := le_of_not_ge hvalue
    have h := neg_le_neg (decodeNat_div_le bits (-value).toNat divisor hdivisor)
    have heq : signedDivUp value divisor =
        -((((-value).toNat / divisor : ℕ)) : ℤ) := by
      simp only [signedDivUp, if_neg hvalue]
    rw [heq, decodeInt_neg_natCast,
      decodeInt_eq_neg_decodeNat_toNat_neg_of_nonpos bits hvalue']
    simpa only [neg_div] using h

namespace NatInterval

/-- Real containment through the project's standard rational-enclosure
semantics. -/
def Contains (interval : NatInterval) (bits : ℕ) (value : ℝ) : Prop :=
  (interval.decode bits).Contains value

theorem point_contains (bits value : ℕ) :
    (point value).Contains bits (decodeNat bits value : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem zero_contains (bits : ℕ) : zero.Contains bits 0 := by
  simpa [zero, decodeNat] using point_contains bits 0

theorem one_contains (bits : ℕ) : one bits |>.Contains bits 1 := by
  constructor <;> norm_num [Contains, decode, one, point, decodeNat, scale,
    RationalEnclosure.Contains]

theorem add_contains {bits : ℕ} {left right : NatInterval}
    {x y : ℝ} (hx : left.Contains bits x) (hy : right.Contains bits y) :
    (left.add right).Contains bits (x + y) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  rcases hy with ⟨hyLower, hyUpper⟩
  constructor
  · change (decodeNat bits (left.lower + right.lower) : ℝ) ≤ x + y
    rw [decodeNat_add_real]
    exact add_le_add hxLower hyLower
  · change x + y ≤ (decodeNat bits (left.upper + right.upper) : ℝ)
    rw [decodeNat_add_real]
    exact add_le_add hxUpper hyUpper

theorem scaleNat_contains {bits coefficient : ℕ} {interval : NatInterval}
    {x : ℝ} (hx : interval.Contains bits x) :
    (interval.scaleNat coefficient).Contains bits ((coefficient : ℝ) * x) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  have hc : (0 : ℝ) ≤ coefficient := by positivity
  constructor
  · have h := mul_le_mul_of_nonneg_left hxLower hc
    change (decodeNat bits (coefficient * interval.lower) : ℝ) ≤
      (coefficient : ℝ) * x
    rw [decodeNat_scaleNat_real]
    exact h
  · have h := mul_le_mul_of_nonneg_left hxUpper hc
    change (coefficient : ℝ) * x ≤
      (decodeNat bits (coefficient * interval.upper) : ℝ)
    rw [decodeNat_scaleNat_real]
    exact h

theorem mul_contains {bits : ℕ} {left right : NatInterval}
    {x y : ℝ} (hx : left.Contains bits x) (hy : right.Contains bits y) :
    (left.mul bits right).Contains bits (x * y) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  rcases hy with ⟨hyLower, hyUpper⟩
  have hx0 : 0 ≤ x := le_trans
    (decodeNat_real_nonnegative bits left.lower) hxLower
  have hy0 : 0 ≤ y := le_trans
    (decodeNat_real_nonnegative bits right.lower) hyLower
  have hroundLower :
      (decodeNat bits (mulDown bits left.lower right.lower) : ℝ) ≤
        (decodeNat bits left.lower : ℝ) *
          (decodeNat bits right.lower : ℝ) := by
    exact_mod_cast decodeNat_mulDown_le bits left.lower right.lower
  have hroundUpper :
      (decodeNat bits left.upper : ℝ) *
          (decodeNat bits right.upper : ℝ) ≤
        (decodeNat bits (mulUp bits left.upper right.upper) : ℝ) := by
    exact_mod_cast decodeNat_le_mulUp bits left.upper right.upper
  constructor
  · norm_num [Contains, decode, mul, RationalEnclosure.Contains] at *
    nlinarith [decodeNat_real_nonnegative bits left.lower,
      decodeNat_real_nonnegative bits right.lower]
  · norm_num [Contains, decode, mul, RationalEnclosure.Contains] at *
    nlinarith [decodeNat_real_nonnegative bits left.upper,
      decodeNat_real_nonnegative bits right.upper]

theorem divNat_contains {bits divisor : ℕ} {interval : NatInterval}
    {x : ℝ} (hdivisor : 0 < divisor) (hx : interval.Contains bits x) :
    (interval.divNat divisor).Contains bits (x / divisor) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  have hd : (0 : ℝ) < divisor := by exact_mod_cast hdivisor
  have hroundLower :
      (decodeNat bits (interval.lower / divisor) : ℝ) ≤
        (decodeNat bits interval.lower : ℝ) / divisor := by
    exact_mod_cast decodeNat_div_le bits interval.lower divisor hdivisor
  have hroundUpper :
      (decodeNat bits interval.upper : ℝ) / divisor ≤
        (decodeNat bits (ceilDiv interval.upper divisor) : ℝ) := by
    exact_mod_cast decodeNat_le_ceilDiv bits interval.upper divisor hdivisor
  constructor
  · change (decodeNat bits (interval.lower / divisor) : ℝ) ≤ x / divisor
    exact le_trans hroundLower ((div_le_div_iff_of_pos_right hd).2 hxLower)
  · change x / divisor ≤
      (decodeNat bits (ceilDiv interval.upper divisor) : ℝ)
    exact le_trans ((div_le_div_iff_of_pos_right hd).2 hxUpper) hroundUpper

end NatInterval

namespace IntInterval

/-- Real containment through the project's standard rational-enclosure
semantics. -/
def Contains (interval : IntInterval) (bits : ℕ) (value : ℝ) : Prop :=
  (interval.decode bits).Contains value

theorem point_contains (bits : ℕ) (value : ℤ) :
    (point value).Contains bits (decodeInt bits value : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem zero_contains (bits : ℕ) : zero.Contains bits 0 := by
  simpa [zero, decodeInt] using point_contains bits 0

theorem add_contains {bits : ℕ} {left right : IntInterval}
    {x y : ℝ} (hx : left.Contains bits x) (hy : right.Contains bits y) :
    (left.add right).Contains bits (x + y) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  rcases hy with ⟨hyLower, hyUpper⟩
  constructor
  · change (decodeInt bits (left.lower + right.lower) : ℝ) ≤ x + y
    rw [decodeInt_add_real]
    exact add_le_add hxLower hyLower
  · change x + y ≤ (decodeInt bits (left.upper + right.upper) : ℝ)
    rw [decodeInt_add_real]
    exact add_le_add hxUpper hyUpper

theorem neg_contains {bits : ℕ} {interval : IntInterval}
    {x : ℝ} (hx : interval.Contains bits x) :
    interval.neg.Contains bits (-x) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  constructor
  · change (decodeInt bits (-interval.upper) : ℝ) ≤ -x
    rw [decodeInt_neg_real]
    exact neg_le_neg hxUpper
  · change -x ≤ (decodeInt bits (-interval.lower) : ℝ)
    rw [decodeInt_neg_real]
    exact neg_le_neg hxLower

theorem sub_contains {bits : ℕ} {left right : IntInterval}
    {x y : ℝ} (hx : left.Contains bits x) (hy : right.Contains bits y) :
    (left.sub right).Contains bits (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_contains hx (neg_contains hy)

theorem scaleNat_contains {bits coefficient : ℕ} {interval : IntInterval}
    {x : ℝ} (hx : interval.Contains bits x) :
    (interval.scaleNat coefficient).Contains bits ((coefficient : ℝ) * x) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  have hc : (0 : ℝ) ≤ coefficient := by positivity
  constructor
  · have h := mul_le_mul_of_nonneg_left hxLower hc
    change (decodeInt bits ((coefficient : ℤ) * interval.lower) : ℝ) ≤
      (coefficient : ℝ) * x
    rw [decodeInt_scaleNat_real]
    exact h
  · have h := mul_le_mul_of_nonneg_left hxUpper hc
    change (coefficient : ℝ) * x ≤
      (decodeInt bits ((coefficient : ℤ) * interval.upper) : ℝ)
    rw [decodeInt_scaleNat_real]
    exact h

theorem mulNonnegative_contains {bits : ℕ}
    {signed : IntInterval} {nonnegative : NatInterval} {x y : ℝ}
    (hx : signed.Contains bits x) (hy : nonnegative.Contains bits y) :
    (signed.mulNonnegative bits nonnegative).Contains bits (x * y) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  rcases hy with ⟨hyLower, hyUpper⟩
  have hy0 : 0 ≤ y := le_trans
    (decodeNat_real_nonnegative bits nonnegative.lower) hyLower
  have hroundLower (endpoint : ℕ) :
      (decodeInt bits (signedMulDown bits signed.lower endpoint) : ℝ) ≤
        (decodeInt bits signed.lower : ℝ) *
          (decodeNat bits endpoint : ℝ) := by
    exact_mod_cast decodeInt_signedMulDown_le bits signed.lower endpoint
  have hroundUpper (endpoint : ℕ) :
      (decodeInt bits signed.upper : ℝ) *
          (decodeNat bits endpoint : ℝ) ≤
        (decodeInt bits (signedMulUp bits signed.upper endpoint) : ℝ) := by
    exact_mod_cast decodeInt_le_signedMulUp bits signed.upper endpoint
  constructor
  · by_cases hl : 0 ≤ signed.lower
    · have hx0 : 0 ≤ x :=
        (decodeInt_real_nonnegative_of_nonnegative bits hl).trans hxLower
      have hbound := (hroundLower nonnegative.lower).trans
        (mul_le_mul hxLower hyLower
          (decodeNat_real_nonnegative bits nonnegative.lower) hx0)
      simpa [Contains, decode, mulNonnegative, hl,
        RationalEnclosure.Contains] using hbound
    · have hl0 := decodeInt_real_nonpositive_of_nonpositive bits (le_of_not_ge hl)
      have hbound := (hroundLower nonnegative.upper).trans <|
        (mul_le_mul_of_nonpos_left hyUpper hl0).trans
          (mul_le_mul_of_nonneg_right hxLower hy0)
      simpa [Contains, decode, mulNonnegative, hl,
        RationalEnclosure.Contains] using hbound
  · by_cases hu : 0 ≤ signed.upper
    ·
      have hu0 := decodeInt_real_nonnegative_of_nonnegative bits hu
      have hbound := (mul_le_mul hxUpper hyUpper hy0 hu0).trans
        (hroundUpper nonnegative.upper)
      simpa [Contains, decode, mulNonnegative, hu,
        RationalEnclosure.Contains] using hbound
    ·
      have hu0 := decodeInt_real_nonpositive_of_nonpositive bits (le_of_not_ge hu)
      have hbound := (mul_le_mul_of_nonneg_right hxUpper hy0).trans <|
        (mul_le_mul_of_nonpos_left hyLower hu0).trans
          (hroundUpper nonnegative.lower)
      simpa [Contains, decode, mulNonnegative, hu,
        RationalEnclosure.Contains] using hbound

theorem divNat_contains {bits divisor : ℕ} {interval : IntInterval}
    {x : ℝ} (hdivisor : 0 < divisor) (hx : interval.Contains bits x) :
    (interval.divNat divisor).Contains bits (x / divisor) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  have hd : (0 : ℝ) < divisor := by exact_mod_cast hdivisor
  have hroundLower :
      (decodeInt bits (signedDivDown interval.lower divisor) : ℝ) ≤
        (decodeInt bits interval.lower : ℝ) / divisor := by
    exact_mod_cast decodeInt_signedDivDown_le bits interval.lower divisor hdivisor
  have hroundUpper :
      (decodeInt bits interval.upper : ℝ) / divisor ≤
        (decodeInt bits (signedDivUp interval.upper divisor) : ℝ) := by
    exact_mod_cast decodeInt_le_signedDivUp bits interval.upper divisor hdivisor
  constructor
  · change (decodeInt bits (signedDivDown interval.lower divisor) : ℝ) ≤
      x / divisor
    exact le_trans hroundLower ((div_le_div_iff_of_pos_right hd).2 hxLower)
  · change x / divisor ≤
      (decodeInt bits (signedDivUp interval.upper divisor) : ℝ)
    exact le_trans ((div_le_div_iff_of_pos_right hd).2 hxUpper) hroundUpper

theorem toSigned_contains {bits : ℕ} {interval : NatInterval} {x : ℝ}
    (hx : interval.Contains bits x) :
    interval.toSigned.Contains bits x := by
  simpa [Contains, NatInterval.Contains, decode, NatInterval.decode,
    NatInterval.toSigned, decodeInt_natCast] using hx

theorem abs_decodeInt_eq_decodeNat_natAbs (bits : ℕ) (value : ℤ) :
    |(decodeInt bits value : ℝ)| =
      (decodeNat bits value.natAbs : ℝ) := by
  have hs : (0 : ℝ) < (scale bits : ℝ) := scale_real_pos bits
  rw [decodeInt, decodeNat]
  norm_num [abs_div, abs_of_pos hs]

theorem decodeNat_mono {bits left right : ℕ} (h : left ≤ right) :
    (decodeNat bits left : ℝ) ≤ (decodeNat bits right : ℝ) := by
  have hq : decodeNat bits left ≤ decodeNat bits right := by
    unfold decodeNat
    apply (div_le_div_iff_of_pos_right (scale_rat_pos bits)).2
    exact_mod_cast h
  exact_mod_cast hq

theorem abs_le_decode_maxAbs {bits : ℕ} {interval : IntInterval} {x : ℝ}
    (hx : interval.Contains bits x) :
    |x| ≤ (decodeNat bits interval.maxAbs : ℝ) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  have hl := decodeNat_mono (bits := bits)
    (Nat.le_max_left interval.lower.natAbs interval.upper.natAbs)
  have hu := decodeNat_mono (bits := bits)
    (Nat.le_max_right interval.lower.natAbs interval.upper.natAbs)
  rw [← abs_decodeInt_eq_decodeNat_natAbs] at hl hu
  rw [abs_le]
  constructor
  · exact le_trans (neg_le_neg hl) (le_trans (neg_abs_le _) hxLower)
  · exact le_trans hxUpper (le_trans (le_abs_self _) hu)

end IntInterval

end LRCompactVFixedDyadic
end CourtadeKumar
