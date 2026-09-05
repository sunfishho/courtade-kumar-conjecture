import InformationTheory.CourtadeKumar.ExactIntervalArithmeticCore
import Mathlib.Tactic.NormNum.BigOperators

/-!
# Executable exact rational logarithm enclosures

This module contains only the rational data and computations used by generated
certificates.  The real-analysis soundness proofs live in `ExactLogEnclosure`,
so arithmetic-only certificate shards need not import the logarithm-analysis
stack.
-/

open Finset

namespace CourtadeKumar
namespace RationalEnclosure

/-- The first `n` positive terms of the odd logarithm series. -/
def atanhPartial (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ range n, q ^ (2 * i + 1) / (2 * i + 1)

/-- A geometric upper bound for the omitted positive tail. -/
def atanhTail (n : ℕ) (q : ℚ) : ℚ :=
  q ^ (2 * n + 1) / (1 - q ^ 2)

/-- Exact rational enclosure for the half-log ratio. -/
def halfLogRatioEnclosure (n : ℕ) (q : ℚ) : RationalEnclosure :=
  ⟨atanhPartial n q, atanhPartial n q + atanhTail n q⟩

/-- The standard range-reduction coordinate `q=(r-1)/(r+1)`. -/
def logRatioCoordinate (r : ℚ) : ℚ :=
  (r - 1) / (r + 1)

/-- Enclose `log r` for a positive rational mantissa `1 ≤ r`. -/
def logMantissaEnclosure (n : ℕ) (r : ℚ) : RationalEnclosure :=
  scale 2 (halfLogRatioEnclosure n (logRatioCoordinate r))

/-- The same positive-series construction specialized to `log 2`. -/
def logTwoEnclosure (n : ℕ) : RationalEnclosure :=
  logMantissaEnclosure n 2

/-- Logarithm enclosure after the exact range reduction `x = 2^e r`. -/
def logScaledMantissaEnclosure (n : ℕ) (e : ℤ) (r : ℚ) :
    RationalEnclosure :=
  add (scale (e : ℚ) (logTwoEnclosure n)) (logMantissaEnclosure n r)

/-- Untrusted range-reduction data for one positive rational endpoint. -/
structure LogRangeCertificate where
  exponent : ℤ
  mantissa : ℚ

def LogRangeCertificate.Valid (x : ℚ)
    (certificate : LogRangeCertificate) : Prop :=
  1 ≤ certificate.mantissa ∧ certificate.mantissa < 2 ∧
    x = (2 : ℚ) ^ certificate.exponent * certificate.mantissa

def LogRangeCertificate.check (x : ℚ)
    (certificate : LogRangeCertificate) : Bool :=
  decide (
    1 ≤ certificate.mantissa ∧ certificate.mantissa < 2 ∧
      x = (2 : ℚ) ^ certificate.exponent * certificate.mantissa)

def LogRangeCertificate.enclosure
    (terms : ℕ) (certificate : LogRangeCertificate) : RationalEnclosure :=
  logScaledMantissaEnclosure terms certificate.exponent certificate.mantissa

/-- Range-reduction certificates for the two endpoints of an input
interval. -/
structure LogIntervalCertificate where
  lower : LogRangeCertificate
  upper : LogRangeCertificate

def LogIntervalCertificate.check
    (input : RationalEnclosure) (certificate : LogIntervalCertificate) : Bool :=
  decide (0 < input.lower) &&
    (certificate.lower.check input.lower && certificate.upper.check input.upper)

def LogIntervalCertificate.enclosure
    (terms : ℕ) (certificate : LogIntervalCertificate) : RationalEnclosure :=
  ⟨(certificate.lower.enclosure terms).lower,
    (certificate.upper.enclosure terms).upper⟩

end RationalEnclosure
end CourtadeKumar
