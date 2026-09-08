import InformationTheory.CourtadeKumar.ExactLogEnclosureCore
import InformationTheory.CourtadeKumar.ExactSqrtEnclosureCore

/-!
# Lightweight deterministic elementary-certificate constructors

These executable square-root and logarithm payload generators depend only on
the elementary enclosure APIs.  Keeping them separate from the high-shape
evaluator lets point-certificate query and replay modules use them without
loading the full high-shape development.

The constructors merely propose rational data.  Their kernel-checked
correctness theorems remain in `LRDeterminantAutoCertificateCorrectness`.
-/

namespace CourtadeKumar
namespace RationalEnclosure

/-- Rational bisection bracket for a proposed square-root payload. -/
def sqrtBracket : ℕ → ℚ → ℚ → ℚ → ℚ × ℚ
  | 0, _x, lo, hi => (lo, hi)
  | fuel + 1, x, lo, hi =>
      let mid := (lo + hi) / 2
      if mid ^ 2 ≤ x then
        sqrtBracket fuel x mid hi
      else
        sqrtBracket fuel x lo mid

/-- Generate an outward square-root certificate by rational bisection. -/
def autoSqrtCertificate (fuel : ℕ) (input : RationalEnclosure) :
    SqrtCertificate :=
  let lowerBracket := sqrtBracket fuel input.lower 0 (max 1 input.lower)
  let upperBracket := sqrtBracket fuel input.upper 0 (max 1 input.upper)
  { lower := lowerBracket.1, upper := upperBracket.2 }

/-- Fuel-bounded exact dyadic normalization.  A failed or insufficiently
normalized proposal is harmless because `LogRangeCertificate.check` rejects
it. -/
def autoLogRangeCertificate : ℕ → ℚ → LogRangeCertificate
  | 0, x => { exponent := 0, mantissa := x }
  | fuel + 1, x =>
      if x < 1 then
        let child := autoLogRangeCertificate fuel (2 * x)
        { exponent := child.exponent - 1, mantissa := child.mantissa }
      else if x < 2 then
        { exponent := 0, mantissa := x }
      else
        let child := autoLogRangeCertificate fuel (x / 2)
        { exponent := child.exponent + 1, mantissa := child.mantissa }

def autoLogIntervalCertificate (fuel : ℕ) (input : RationalEnclosure) :
    LogIntervalCertificate :=
  { lower := autoLogRangeCertificate fuel input.lower
    upper := autoLogRangeCertificate fuel input.upper }

end RationalEnclosure
end CourtadeKumar
