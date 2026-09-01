import InformationTheory.CourtadeKumar.RationalEnclosureCore

/-!
# Fixed-dyadic interval arithmetic for compact-V Taylor evaluators

This is the proof-free executable layer.  Every stored endpoint is an integer
numerator over the common implicit denominator `2^bits`.  Multiplication
rounds back to that denominator immediately, so recursive evaluators never
construct growing rational denominators.

The nonnegative and signed interval types are deliberately separate.  The
centered compact-`V` jet has many nonnegative powers and shape factors, but
its polynomial coefficients and derivative accumulators are signed.  The
mixed multiplication below is therefore the only signed product needed by
the eventual evaluator.

All interpretation and rounding proofs live in
`LRCompactVFixedDyadicIntervalSound`.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVFixedDyadic

/-- The common natural-number denominator. -/
def scale (bits : ℕ) : ℕ :=
  2 ^ bits

/-- Decode a nonnegative fixed-dyadic numerator as an exact rational. -/
def decodeNat (bits value : ℕ) : ℚ :=
  (value : ℚ) / (scale bits : ℚ)

/-- Decode a signed fixed-dyadic numerator as an exact rational. -/
def decodeInt (bits : ℕ) (value : ℤ) : ℚ :=
  (value : ℚ) / (scale bits : ℚ)

/-- A nonnegative interval with an implicit common dyadic denominator. -/
structure NatInterval where
  lower : ℕ
  upper : ℕ
  deriving DecidableEq, Repr

/-- A signed interval with an implicit common dyadic denominator. -/
structure IntInterval where
  lower : ℤ
  upper : ℤ
  deriving DecidableEq, Repr

/-- Floor division by the dyadic scale. -/
def mulDown (bits left right : ℕ) : ℕ :=
  Nat.shiftRight (left * right) bits

/-- Natural-number ceiling division.  Soundness assumes a positive divisor. -/
def ceilDiv (value divisor : ℕ) : ℕ :=
  (value + divisor - 1) / divisor

/-- Ceiling division by the dyadic scale. -/
def mulUp (bits left right : ℕ) : ℕ :=
  Nat.shiftRight (left * right + scale bits - 1) bits

/-- Multiply a signed numerator by a nonnegative numerator and round down. -/
def signedMulDown (bits : ℕ) (signed : ℤ) (nonnegative : ℕ) : ℤ :=
  if 0 ≤ signed then
    (mulDown bits signed.toNat nonnegative : ℤ)
  else
    -((mulUp bits (-signed).toNat nonnegative : ℕ) : ℤ)

/-- Multiply a signed numerator by a nonnegative numerator and round up. -/
def signedMulUp (bits : ℕ) (signed : ℤ) (nonnegative : ℕ) : ℤ :=
  if 0 ≤ signed then
    (mulUp bits signed.toNat nonnegative : ℤ)
  else
    -((mulDown bits (-signed).toNat nonnegative : ℕ) : ℤ)

/-- Divide a signed fixed-dyadic numerator by a positive natural and round
down, retaining the same implicit dyadic denominator. -/
def signedDivDown (value : ℤ) (divisor : ℕ) : ℤ :=
  if 0 ≤ value then
    ((value.toNat / divisor : ℕ) : ℤ)
  else
    -((ceilDiv (-value).toNat divisor : ℕ) : ℤ)

/-- Divide a signed fixed-dyadic numerator by a positive natural and round
up, retaining the same implicit dyadic denominator. -/
def signedDivUp (value : ℤ) (divisor : ℕ) : ℤ :=
  if 0 ≤ value then
    ((ceilDiv value.toNat divisor : ℕ) : ℤ)
  else
    -(((-value).toNat / divisor : ℕ) : ℤ)

namespace NatInterval

def point (value : ℕ) : NatInterval :=
  ⟨value, value⟩

def zero : NatInterval :=
  point 0

def one (bits : ℕ) : NatInterval :=
  point (scale bits)

/-- Decode both endpoints without performing any arithmetic reduction in the
generated checker. -/
def decode (bits : ℕ) (interval : NatInterval) : RationalEnclosure :=
  ⟨decodeNat bits interval.lower, decodeNat bits interval.upper⟩

def add (left right : NatInterval) : NatInterval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

/-- Exact multiplication by a natural coefficient at the stored scale. -/
def scaleNat (coefficient : ℕ) (interval : NatInterval) : NatInterval :=
  ⟨coefficient * interval.lower, coefficient * interval.upper⟩

/-- Outward product for two intervals known to represent nonnegative values. -/
def mul (bits : ℕ) (left right : NatInterval) : NatInterval :=
  ⟨mulDown bits left.lower right.lower,
    mulUp bits left.upper right.upper⟩

/-- Division by a positive small natural, with outward endpoint rounding. -/
def divNat (interval : NatInterval) (divisor : ℕ) : NatInterval :=
  ⟨interval.lower / divisor, ceilDiv interval.upper divisor⟩

/-- Regard a nonnegative interval as a signed interval without changing its
stored endpoints. -/
def toSigned (interval : NatInterval) : IntInterval :=
  ⟨interval.lower, interval.upper⟩

end NatInterval

namespace IntInterval

def point (value : ℤ) : IntInterval :=
  ⟨value, value⟩

def zero : IntInterval :=
  point 0

/-- Decode both endpoints without changing their common denominator. -/
def decode (bits : ℕ) (interval : IntInterval) : RationalEnclosure :=
  ⟨decodeInt bits interval.lower, decodeInt bits interval.upper⟩

def add (left right : IntInterval) : IntInterval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

def neg (interval : IntInterval) : IntInterval :=
  ⟨-interval.upper, -interval.lower⟩

def sub (left right : IntInterval) : IntInterval :=
  add left (neg right)

/-- Exact multiplication by a nonnegative natural coefficient. -/
def scaleNat (coefficient : ℕ) (interval : IntInterval) : IntInterval :=
  ⟨(coefficient : ℤ) * interval.lower,
    (coefficient : ℤ) * interval.upper⟩

/-- Outward product of a signed interval and a nonnegative interval.  Only
the sign of each signed endpoint is needed to select the extremal
nonnegative endpoint. -/
def mulNonnegative (bits : ℕ)
    (signed : IntInterval) (nonnegative : NatInterval) : IntInterval :=
  let lower :=
    if 0 ≤ signed.lower then
      signedMulDown bits signed.lower nonnegative.lower
    else
      signedMulDown bits signed.lower nonnegative.upper
  let upper :=
    if 0 ≤ signed.upper then
      signedMulUp bits signed.upper nonnegative.upper
    else
      signedMulUp bits signed.upper nonnegative.lower
  ⟨lower, upper⟩

/-- Outward division by a positive small natural. -/
def divNat (interval : IntInterval) (divisor : ℕ) : IntInterval :=
  ⟨signedDivDown interval.lower divisor,
    signedDivUp interval.upper divisor⟩

/-- Fixed-scale numerator bounding the absolute value of every point in the
interval, provided the interval is ordered. -/
def maxAbs (interval : IntInterval) : ℕ :=
  max interval.lower.natAbs interval.upper.natAbs

end IntInterval

end LRCompactVFixedDyadic
end CourtadeKumar
