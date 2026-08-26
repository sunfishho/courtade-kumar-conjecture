import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate

/-!
# Exact rational interval arithmetic

Small, compositional interval operations for the kernel-checked certificate
engine.  Every operation is paired with a theorem over `ℝ`; computation of
the rational endpoints is therefore separated from the semantic proof that
they contain the intended real value.
-/

namespace CourtadeKumar
namespace RationalEnclosure

/-- The degenerate interval at an exact rational point. -/
def point (q : ℚ) : RationalEnclosure := ⟨q, q⟩

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

/-- Exact Minkowski addition of rational intervals. -/
def add (a b : RationalEnclosure) : RationalEnclosure :=
  ⟨a.lower + b.lower, a.upper + b.upper⟩

theorem contains_add {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (add a b).Contains (x + y) := by
  constructor
  · simpa [add, Contains] using add_le_add hx.1 hy.1
  · simpa [add, Contains] using add_le_add hx.2 hy.2

/-- Reflection of an interval through zero. -/
def neg (a : RationalEnclosure) : RationalEnclosure :=
  ⟨-a.upper, -a.lower⟩

theorem contains_neg {a : RationalEnclosure} {x : ℝ}
    (hx : a.Contains x) :
    (neg a).Contains (-x) := by
  constructor
  · simpa [neg, Contains] using neg_le_neg hx.2
  · simpa [neg, Contains] using neg_le_neg hx.1

/-- Exact Minkowski subtraction of rational intervals. -/
def sub (a b : RationalEnclosure) : RationalEnclosure :=
  add a (neg b)

theorem contains_sub {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (sub a b).Contains (x - y) := by
  simpa [sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- Product enclosure for intervals known to be nonnegative. -/
def mulNonnegative (a b : RationalEnclosure) : RationalEnclosure :=
  ⟨a.lower * b.lower, a.upper * b.upper⟩

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

/-- Reciprocal enclosure for an interval bounded strictly away from zero. -/
def invPositive (a : RationalEnclosure) : RationalEnclosure :=
  ⟨a.upper⁻¹, a.lower⁻¹⟩

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

/-- Quotient enclosure when numerator and denominator intervals are
nonnegative and the denominator is strictly positive. -/
def divNonnegative (a b : RationalEnclosure) : RationalEnclosure :=
  mulNonnegative a (invPositive b)

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

end RationalEnclosure
end CourtadeKumar
