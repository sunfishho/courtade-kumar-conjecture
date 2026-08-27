import InformationTheory.CourtadeKumar.ExactIntervalArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact rational enclosures for logarithms

The interval verifier reduces logarithms to

`(1 / 2) * log ((1 + q) / (1 - q))`

with `0 ≤ q < 1`.  Mathlib's proved positive-series bounds turn a finite
rational sum and rational geometric tail into a kernel-checked enclosure.
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

theorem contains_halfLogRatioEnclosure
    (n : ℕ) {q : ℚ} (hq0 : (0 : ℚ) ≤ q) (hq1 : q < 1) :
    (halfLogRatioEnclosure n q).Contains
      (1 / 2 * Real.log ((1 + (q : ℝ)) / (1 - (q : ℝ)))) := by
  have hq0Real : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hq1Real : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hlower := Real.sum_range_le_log_div hq0Real hq1Real n
  have hupper := Real.log_div_le_sum_range_add hq0Real hq1Real n
  constructor
  · simpa [halfLogRatioEnclosure, atanhPartial, Contains] using hlower
  · simpa [halfLogRatioEnclosure, atanhPartial, atanhTail, Contains] using hupper

/-- The standard range-reduction coordinate `q=(r-1)/(r+1)`. -/
def logRatioCoordinate (r : ℚ) : ℚ :=
  (r - 1) / (r + 1)

/-- Enclose `log r` for a positive rational mantissa `1 ≤ r`. -/
def logMantissaEnclosure (n : ℕ) (r : ℚ) : RationalEnclosure :=
  scale 2 (halfLogRatioEnclosure n (logRatioCoordinate r))

theorem contains_logMantissaEnclosure
    (n : ℕ) {r : ℚ} (hr : (1 : ℚ) ≤ r) :
    (logMantissaEnclosure n r).Contains (Real.log (r : ℝ)) := by
  have hrPos : (0 : ℚ) < r := zero_lt_one.trans_le hr
  have hrPlus : (0 : ℚ) < r + 1 := by linarith
  have hq0 : (0 : ℚ) ≤ logRatioCoordinate r := by
    exact div_nonneg (sub_nonneg.mpr hr) hrPlus.le
  have hq1 : logRatioCoordinate r < 1 := by
    rw [logRatioCoordinate, div_lt_one hrPlus]
    linarith
  have hratio :
      ((1 + (logRatioCoordinate r : ℚ)) /
        (1 - logRatioCoordinate r) : ℚ) = r := by
    rw [logRatioCoordinate]
    field_simp
    ring
  have hcontains := contains_scale (2 : ℚ)
    (contains_halfLogRatioEnclosure n hq0 hq1)
  have hratioReal :
      (1 + (logRatioCoordinate r : ℝ)) /
        (1 - (logRatioCoordinate r : ℝ)) = (r : ℝ) := by
    exact_mod_cast hratio
  simpa [logMantissaEnclosure, hratioReal] using hcontains

/-- The same positive-series construction specialized to `log 2`. -/
def logTwoEnclosure (n : ℕ) : RationalEnclosure :=
  logMantissaEnclosure n 2

theorem contains_logTwoEnclosure (n : ℕ) :
    (logTwoEnclosure n).Contains (Real.log 2) := by
  exact contains_logMantissaEnclosure n (by norm_num)

/-- Logarithm enclosure after the exact range reduction `x = 2^e r`. -/
def logScaledMantissaEnclosure (n : ℕ) (e : ℤ) (r : ℚ) :
    RationalEnclosure :=
  add (scale (e : ℚ) (logTwoEnclosure n)) (logMantissaEnclosure n r)

theorem contains_logScaledMantissaEnclosure
    (n : ℕ) (e : ℤ) {r : ℚ} (hr : (1 : ℚ) ≤ r) :
    (logScaledMantissaEnclosure n e r).Contains
      (Real.log (((2 : ℝ) ^ e) * (r : ℝ))) := by
  have htwo := contains_scale (e : ℚ) (contains_logTwoEnclosure n)
  have hrlog := contains_logMantissaEnclosure n hr
  have hsum := contains_add htwo hrlog
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℚ) < r := zero_lt_one.trans_le hr
    exact_mod_cast this.ne'
  have hpow0 : (2 : ℝ) ^ e ≠ 0 := zpow_ne_zero e (by norm_num)
  have hformula :
      Real.log (((2 : ℝ) ^ e) * (r : ℝ)) =
        (e : ℝ) * Real.log 2 + Real.log (r : ℝ) := by
    rw [Real.log_mul hpow0 hr0, Real.log_zpow]
  rw [hformula]
  simpa [logScaledMantissaEnclosure] using hsum

/-- A supplied exact range-reduction identity transports the enclosure to
the original positive rational input.  A concrete checker can verify `hx`
by rational computation. -/
theorem contains_log_of_rangeReduction
    (n : ℕ) (e : ℤ) {r x : ℚ} (hr : (1 : ℚ) ≤ r)
    (hx : x = (2 : ℚ) ^ e * r) :
    (logScaledMantissaEnclosure n e r).Contains (Real.log (x : ℝ)) := by
  have h := contains_logScaledMantissaEnclosure n e hr
  have hxReal : (x : ℝ) = (2 : ℝ) ^ e * (r : ℝ) := by
    have hxCast := congrArg (fun q : ℚ ↦ (q : ℝ)) hx
    norm_num at hxCast ⊢
    exact hxCast
  simpa [hxReal] using h

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

theorem LogRangeCertificate.sound
    (terms : ℕ) {x : ℚ} {certificate : LogRangeCertificate}
    (hcheck : certificate.check x = true) :
    (certificate.enclosure terms).Contains (Real.log (x : ℝ)) := by
  have hvalid : certificate.Valid x := by
    simpa [LogRangeCertificate.check, LogRangeCertificate.Valid] using hcheck
  exact contains_log_of_rangeReduction terms certificate.exponent
    hvalid.1 hvalid.2.2

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

theorem LogIntervalCertificate.sound
    (terms : ℕ) {input : RationalEnclosure}
    {certificate : LogIntervalCertificate}
    (hcheck : certificate.check input = true)
    {x : ℝ} (hx : input.Contains x) :
    (certificate.enclosure terms).Contains (Real.log x) := by
  have hparts :
      (0 : ℚ) < input.lower ∧
      certificate.lower.check input.lower = true ∧
      certificate.upper.check input.upper = true := by
    simpa [LogIntervalCertificate.check] using hcheck
  have hlowerCheck : certificate.lower.check input.lower = true :=
    hparts.2.1
  have hupperCheck : certificate.upper.check input.upper = true :=
    hparts.2.2
  have hlowerPositiveRat : (0 : ℚ) < input.lower := by
    simpa using hparts.1
  have hlower := certificate.lower.sound terms hlowerCheck
  have hupper := certificate.upper.sound terms hupperCheck
  have hlowerPos : (0 : ℝ) < (input.lower : ℝ) := by
    exact_mod_cast hlowerPositiveRat
  have hxPos : 0 < x := hlowerPos.trans_le hx.1
  have hlogLower : Real.log (input.lower : ℝ) ≤ Real.log x :=
    Real.log_le_log hlowerPos hx.1
  have hlogUpper : Real.log x ≤ Real.log (input.upper : ℝ) :=
    Real.log_le_log hxPos hx.2
  exact ⟨hlower.1.trans hlogLower, hlogUpper.trans hupper.2⟩

end RationalEnclosure
end CourtadeKumar
