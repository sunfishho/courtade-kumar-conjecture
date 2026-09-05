import InformationTheory.CourtadeKumar.ExactIntervalArithmeticCore
import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact rational interval arithmetic

Small, compositional interval operations for the kernel-checked certificate
engine.  Every operation is paired with a theorem over `ℝ`; computation of
the rational endpoints is therefore separated from the semantic proof that
they contain the intended real value.
-/

namespace CourtadeKumar
namespace RationalEnclosure

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem contains_add {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (add a b).Contains (x + y) := by
  constructor
  · simpa [add, Contains] using add_le_add hx.1 hy.1
  · simpa [add, Contains] using add_le_add hx.2 hy.2

theorem contains_neg {a : RationalEnclosure} {x : ℝ}
    (hx : a.Contains x) :
    (neg a).Contains (-x) := by
  constructor
  · simpa [neg, Contains] using neg_le_neg hx.2
  · simpa [neg, Contains] using neg_le_neg hx.1

theorem contains_sub {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (sub a b).Contains (x - y) := by
  simpa [sub_eq_add_neg] using contains_add hx (contains_neg hy)

theorem radius_nonnegative {a : RationalEnclosure} {x : ℝ}
    (hx : a.Contains x) :
    (0 : ℚ) ≤ radius a := by
  have hvalidReal : (a.lower : ℝ) ≤ (a.upper : ℝ) := hx.1.trans hx.2
  have hvalid : a.lower ≤ a.upper := by exact_mod_cast hvalidReal
  simp only [radius]
  exact div_nonneg (sub_nonneg.mpr hvalid) (by norm_num)

theorem abs_sub_center_le_radius
    {a : RationalEnclosure} {x : ℝ} (hx : a.Contains x) :
    |x - (center a : ℝ)| ≤ (radius a : ℝ) := by
  rw [abs_le]
  rcases hx with ⟨hxLo, hxHi⟩
  constructor <;> norm_num [center, radius] at * <;> linarith

theorem contains_mul {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (mul a b).Contains (x * y) := by
  let ca : ℝ := center a
  let cb : ℝ := center b
  let ra : ℝ := radius a
  let rb : ℝ := radius b
  have hra : 0 ≤ ra := by
    change (0 : ℝ) ≤ (radius a : ℝ)
    exact_mod_cast (radius_nonnegative hx)
  have hrb : 0 ≤ rb := by
    change (0 : ℝ) ≤ (radius b : ℝ)
    exact_mod_cast (radius_nonnegative hy)
  have hxa : |x - ca| ≤ ra := abs_sub_center_le_radius hx
  have hyb : |y - cb| ≤ rb := abs_sub_center_le_radius hy
  have hcx : |ca| * |y - cb| ≤ |ca| * rb :=
    mul_le_mul_of_nonneg_left hyb (abs_nonneg ca)
  have hcy : |cb| * |x - ca| ≤ |cb| * ra :=
    mul_le_mul_of_nonneg_left hxa (abs_nonneg cb)
  have hxy : |x - ca| * |y - cb| ≤ ra * rb :=
    mul_le_mul hxa hyb (abs_nonneg _) hra
  have herror :
      |x * y - ca * cb| ≤ |ca| * rb + |cb| * ra + ra * rb := by
    calc
      |x * y - ca * cb| =
          |ca * (y - cb) + cb * (x - ca) + (x - ca) * (y - cb)| := by
            congr 1
            ring
      _ ≤ |ca * (y - cb)| + |cb * (x - ca)| +
          |(x - ca) * (y - cb)| := by
            calc
              _ ≤ |ca * (y - cb) + cb * (x - ca)| +
                    |(x - ca) * (y - cb)| := abs_add_le _ _
              _ ≤ (|ca * (y - cb)| + |cb * (x - ca)|) +
                    |(x - ca) * (y - cb)| :=
                  add_le_add (abs_add_le _ _) le_rfl
      _ = |ca| * |y - cb| + |cb| * |x - ca| +
          |x - ca| * |y - cb| := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |ca| * rb + |cb| * ra + ra * rb :=
        add_le_add (add_le_add hcx hcy) hxy
  have hbounds := (abs_le.mp herror)
  change
    (((center a * center b -
        (|center a| * radius b + |center b| * radius a +
          radius a * radius b) : ℚ) : ℝ) ≤ x * y) ∧
      x * y ≤
        ((center a * center b +
          (|center a| * radius b + |center b| * radius a +
            radius a * radius b) : ℚ) : ℝ)
  norm_num at hbounds ⊢
  constructor <;> linarith

theorem contains_scale (q : ℚ) {a : RationalEnclosure} {x : ℝ}
    (hx : a.Contains x) :
    (scale q a).Contains ((q : ℝ) * x) := by
  exact contains_mul (contains_point q) hx

theorem contains_square {a : RationalEnclosure} {x : ℝ}
    (hx : a.Contains x) :
    (square a).Contains (x ^ 2) := by
  simpa [square, pow_two] using contains_mul hx hx

theorem contains_pow {a : RationalEnclosure} {x : ℝ}
    (hx : a.Contains x) :
    ∀ n, (pow a n).Contains (x ^ n)
  | 0 => by simpa [pow] using contains_point 1
  | n + 1 => by
      simpa [pow, pow_succ] using contains_mul (contains_pow hx n) hx

theorem contains_mulNonnegative
    {a b : RationalEnclosure} {x y : ℝ}
    (ha : (0 : ℚ) ≤ a.lower) (hb : (0 : ℚ) ≤ b.lower)
    (hx : a.Contains x) (hy : b.Contains y) :
    (mulNonnegative a b).Contains (x * y) := by
  have ha0 : (0 : ℝ) ≤ (a.lower : ℝ) := by exact_mod_cast ha
  have hb0 : (0 : ℝ) ≤ (b.lower : ℝ) := by exact_mod_cast hb
  have hx0 : 0 ≤ x := ha0.trans hx.1
  have hy0 : 0 ≤ y := hb0.trans hy.1
  have haUpper0 : (0 : ℝ) ≤ (a.upper : ℝ) := hx0.trans hx.2
  have hbUpper0 : (0 : ℝ) ≤ (b.upper : ℝ) := hy0.trans hy.2
  constructor
  · simpa [mulNonnegative, Contains] using
      mul_le_mul hx.1 hy.1 hb0 hx0
  · simpa [mulNonnegative, Contains] using
      mul_le_mul hx.2 hy.2 hy0 haUpper0

theorem contains_invPositive
    {a : RationalEnclosure} {x : ℝ}
    (ha : (0 : ℚ) < a.lower) (hx : a.Contains x) :
    (invPositive a).Contains x⁻¹ := by
  have ha0 : (0 : ℝ) < (a.lower : ℝ) := by exact_mod_cast ha
  have hx0 : 0 < x := ha0.trans_le hx.1
  have haUpper0 : (0 : ℝ) < (a.upper : ℝ) := hx0.trans_le hx.2
  constructor
  · simpa [invPositive, Contains] using
      (inv_le_inv₀ haUpper0 hx0).2 hx.2
  · simpa [invPositive, Contains] using
      (inv_le_inv₀ hx0 ha0).2 hx.1

theorem contains_divNonnegative
    {a b : RationalEnclosure} {x y : ℝ}
    (ha : (0 : ℚ) ≤ a.lower) (hb : (0 : ℚ) < b.lower)
    (hx : a.Contains x) (hy : b.Contains y) :
    (divNonnegative a b).Contains (x / y) := by
  have hbUpper : (0 : ℚ) < b.upper := by
    have hb0 : (0 : ℝ) < (b.lower : ℝ) := by exact_mod_cast hb
    have hy0 : 0 < y := hb0.trans_le hy.1
    have hUpper0 : (0 : ℝ) < (b.upper : ℝ) := hy0.trans_le hy.2
    exact_mod_cast hUpper0
  have hinvLower : (0 : ℚ) ≤ (invPositive b).lower := by
    simp [invPositive, hbUpper.le]
  simpa [divNonnegative, div_eq_mul_inv] using
    contains_mulNonnegative ha hinvLower hx (contains_invPositive hb hy)

theorem contains_div {a b : RationalEnclosure} {x y : ℝ}
    (hb : (0 : ℚ) < b.lower)
    (hx : a.Contains x) (hy : b.Contains y) :
    (div a b).Contains (x / y) := by
  simpa [div, div_eq_mul_inv] using
    contains_mul hx (contains_invPositive hb hy)

end RationalEnclosure
end CourtadeKumar
