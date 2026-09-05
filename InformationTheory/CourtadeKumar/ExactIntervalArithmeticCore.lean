import InformationTheory.CourtadeKumar.RationalEnclosureCore

/-!
# Executable exact rational interval arithmetic

This file contains only endpoint computations.  Their real-valued containment
theorems remain in `ExactIntervalArithmetic`, so generated arithmetic shards
do not load real analysis or proof tactics.
-/

namespace CourtadeKumar
namespace RationalEnclosure

/-- The degenerate interval at an exact rational point. -/
def point (q : ℚ) : RationalEnclosure := ⟨q, q⟩

/-- Exact Minkowski addition of rational intervals. -/
def add (a b : RationalEnclosure) : RationalEnclosure :=
  ⟨a.lower + b.lower, a.upper + b.upper⟩

/-- Reflection of an interval through zero. -/
def neg (a : RationalEnclosure) : RationalEnclosure :=
  ⟨-a.upper, -a.lower⟩

/-- Exact Minkowski subtraction of rational intervals. -/
def sub (a b : RationalEnclosure) : RationalEnclosure :=
  add a (neg b)

/-- Rational midpoint of an enclosure. -/
def center (a : RationalEnclosure) : ℚ :=
  (a.lower + a.upper) / 2

/-- Rational half-width of an enclosure. -/
def radius (a : RationalEnclosure) : ℚ :=
  (a.upper - a.lower) / 2

/-- A signed product enclosure in midpoint-radius form. -/
def mul (a b : RationalEnclosure) : RationalEnclosure :=
  let c := center a * center b
  let r := |center a| * radius b + |center b| * radius a +
    radius a * radius b
  ⟨c - r, c + r⟩

/-- Multiplication by an exact rational scalar. -/
def scale (q : ℚ) (a : RationalEnclosure) : RationalEnclosure :=
  mul (point q) a

/-- A square enclosure. -/
def square (a : RationalEnclosure) : RationalEnclosure :=
  mul a a

/-- Executable natural powers of an enclosure. -/
def pow : RationalEnclosure → ℕ → RationalEnclosure
  | _, 0 => point 1
  | a, n + 1 => mul (pow a n) a

/-- Product enclosure for intervals known to be nonnegative. -/
def mulNonnegative (a b : RationalEnclosure) : RationalEnclosure :=
  ⟨a.lower * b.lower, a.upper * b.upper⟩

/-- Reciprocal enclosure for an interval bounded strictly away from zero. -/
def invPositive (a : RationalEnclosure) : RationalEnclosure :=
  ⟨a.upper⁻¹, a.lower⁻¹⟩

/-- Quotient enclosure when numerator and denominator are nonnegative. -/
def divNonnegative (a b : RationalEnclosure) : RationalEnclosure :=
  mulNonnegative a (invPositive b)

/-- General signed quotient enclosure with a positive denominator. -/
def div (a b : RationalEnclosure) : RationalEnclosure :=
  mul a (invPositive b)

end RationalEnclosure
end CourtadeKumar
