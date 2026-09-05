import Mathlib.Algebra.Order.Field.Rat

/-!
# Executable rational-enclosure data

The point-certificate compiler needs only a pair of rational endpoints.  The
interpretation of those endpoints as a set of real numbers lives in
`IntervalSubdivisionCertificate`, outside arithmetic-only import closures.
-/

namespace CourtadeKumar

/-- An exact rational enclosure. -/
structure RationalEnclosure where
  lower : ℚ
  upper : ℚ

end CourtadeKumar
