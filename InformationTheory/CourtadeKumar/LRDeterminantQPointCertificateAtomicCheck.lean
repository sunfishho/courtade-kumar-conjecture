import InformationTheory.CourtadeKumar.LRCertificateQEnclosureCore

/-!
# Factored checks for literal `Q/Q'` point certificates

A generated point certificate contains several independent exact-rational
checks.  Reducing the complete `LRQPointCertificate.primeCheck` expression at
once can require a much deeper native process stack than any individual
check.  The lemmas here reassemble the original Boolean checker from atomic
kernel-checked equalities.  They add no alternative acceptance condition and
perform no arithmetic themselves.
-/

namespace CourtadeKumar
namespace RationalEnclosure

/-- A successful range-reduction check already proves that its input is
positive: it is a positive integral power of two times a mantissa at least
one. -/
theorem LogRangeCertificate.input_pos_of_check {input : ℚ}
    {certificate : LogRangeCertificate}
    (hcheck : certificate.check input = true) :
    0 < input := by
  have hvalid : certificate.Valid input := by
    simpa [LogRangeCertificate.check, LogRangeCertificate.Valid] using hcheck
  rw [hvalid.2.2]
  exact mul_pos (zpow_pos (by norm_num) certificate.exponent)
    (zero_lt_one.trans_le hvalid.1)

/-- Reassemble a logarithm-interval check from its input-positivity check and
the two endpoint range-reduction checks. -/
theorem LogIntervalCertificate.check_of_atomic
    {input : RationalEnclosure}
    {certificate : LogIntervalCertificate}
    (hpositive : decide ((0 : ℚ) < input.lower) = true)
    (hlower : certificate.lower.check input.lower = true)
    (hupper : certificate.upper.check input.upper = true) :
    certificate.check input = true := by
  simp only [LogIntervalCertificate.check, Bool.and_eq_true]
  exact ⟨hpositive, hlower, hupper⟩

/-- Reassemble a logarithm-interval check from its two range-reduction
checks.  Positivity of the lower input follows from the first check, so a
generated certificate need not reduce that comparison separately. -/
theorem LogIntervalCertificate.check_of_range_checks
    {input : RationalEnclosure}
    {certificate : LogIntervalCertificate}
    (hlower : certificate.lower.check input.lower = true)
    (hupper : certificate.upper.check input.upper = true) :
    certificate.check input = true := by
  apply check_of_atomic ?_ hlower hupper
  simpa only [decide_eq_true_eq] using
    LogRangeCertificate.input_pos_of_check hlower

end RationalEnclosure

namespace LRQPointCertificate

/-- The lower endpoint of the lower probability interval is determined by
the upper square-root endpoint. -/
theorem lowerProbability_lower_eq (certificate : LRQPointCertificate) :
    certificate.lowerProbability.lower =
      (1 - certificate.sqrtOneSub.upper) / 2 := by
  norm_num [lowerProbability, sqrtEnclosure,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.sub, RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

/-- The upper endpoint of the lower probability interval is determined by
the lower square-root endpoint. -/
theorem lowerProbability_upper_eq (certificate : LRQPointCertificate) :
    certificate.lowerProbability.upper =
      (1 - certificate.sqrtOneSub.lower) / 2 := by
  norm_num [lowerProbability, sqrtEnclosure,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.sub, RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

/-- The lower endpoint of the upper probability interval is determined by
the lower square-root endpoint. -/
theorem upperProbability_lower_eq (certificate : LRQPointCertificate) :
    certificate.upperProbability.lower =
      (1 + certificate.sqrtOneSub.lower) / 2 := by
  norm_num [upperProbability, sqrtEnclosure,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

/-- The upper endpoint of the upper probability interval is determined by
the upper square-root endpoint. -/
theorem upperProbability_upper_eq (certificate : LRQPointCertificate) :
    certificate.upperProbability.upper =
      (1 + certificate.sqrtOneSub.upper) / 2 := by
  norm_num [upperProbability, sqrtEnclosure,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

/-- The six independent Boolean facts making up a derivative point check.
Keeping them as record fields lets generated code expose one declaration per
point while each field remains a separate reduction goal. -/
structure AtomicChecks (y : ℚ) (certificate : LRQPointCertificate) : Prop where
  sqrt : certificate.sqrtOneSub.check (sqrtInput y) = true
  lowerLower : certificate.logLowerProbability.lower.check
    certificate.lowerProbability.lower = true
  lowerUpper : certificate.logLowerProbability.upper.check
    certificate.lowerProbability.upper = true
  upperLower : certificate.logUpperProbability.lower.check
    certificate.upperProbability.lower = true
  upperUpper : certificate.logUpperProbability.upper.check
    certificate.upperProbability.upper = true
  sqrtPositive :
    decide ((0 : ℚ) < certificate.sqrtEnclosure.lower) = true

/-- Reassemble the original derivative point checker from six independent
Boolean equalities.  Generated proofs can place every arithmetic reduction in
its own declaration and use this theorem for the shallow final assembly. -/
theorem primeCheck_of_atomic {y : ℚ} {certificate : LRQPointCertificate}
    (hsqrt : certificate.sqrtOneSub.check (sqrtInput y) = true)
    (hlowerLower : certificate.logLowerProbability.lower.check
      certificate.lowerProbability.lower = true)
    (hlowerUpper : certificate.logLowerProbability.upper.check
      certificate.lowerProbability.upper = true)
    (hupperLower : certificate.logUpperProbability.lower.check
      certificate.upperProbability.lower = true)
    (hupperUpper : certificate.logUpperProbability.upper.check
      certificate.upperProbability.upper = true)
    (hsqrtPositive :
      decide ((0 : ℚ) < certificate.sqrtEnclosure.lower) = true) :
    certificate.primeCheck y = true := by
  have hlowerCheck : certificate.logLowerProbability.check
      certificate.lowerProbability = true :=
    RationalEnclosure.LogIntervalCertificate.check_of_range_checks
      hlowerLower hlowerUpper
  have hupperCheck : certificate.logUpperProbability.check
      certificate.upperProbability = true :=
    RationalEnclosure.LogIntervalCertificate.check_of_range_checks
      hupperLower hupperUpper
  have hcheck : certificate.check y = true := by
    simp only [check, Bool.and_eq_true]
    exact ⟨⟨hsqrt, hlowerCheck⟩, hupperCheck⟩
  simp only [primeCheck, Bool.and_eq_true]
  exact ⟨hcheck, hsqrtPositive⟩

/-- A record of independently reduced atomic facts implies the original
monolithic checker. -/
theorem AtomicChecks.toPrimeCheck {y : ℚ}
    {certificate : LRQPointCertificate}
    (checks : AtomicChecks y certificate) :
    certificate.primeCheck y = true :=
  primeCheck_of_atomic checks.sqrt checks.lowerLower checks.lowerUpper
    checks.upperLower checks.upperUpper checks.sqrtPositive

/-- The atomic checks already force the point into the analytic domain.  This
removes a separate generated rational-range proof for every cached point. -/
theorem AtomicChecks.inRange {y : ℚ}
    {certificate : LRQPointCertificate}
    (checks : AtomicChecks y certificate) :
    y ∈ Set.Ioo (0 : ℚ) 1 := by
  have hsqrtFacts :
      (0 : ℚ) ≤ (sqrtInput y).lower ∧
      (sqrtInput y).lower ≤ (sqrtInput y).upper ∧
      0 ≤ certificate.sqrtOneSub.lower ∧
      certificate.sqrtOneSub.lower ^ 2 ≤ (sqrtInput y).lower ∧
      0 ≤ certificate.sqrtOneSub.upper ∧
      (sqrtInput y).upper ≤ certificate.sqrtOneSub.upper ^ 2 := by
    simpa [RationalEnclosure.SqrtCertificate.check] using checks.sqrt
  rcases hsqrtFacts with
    ⟨_, _, hrootLowerNonnegative, hrootLowerSq,
      hrootUpperNonnegative, hrootUpperSq⟩
  have hrootLowerPositive : (0 : ℚ) < certificate.sqrtOneSub.lower := by
    have hpositive : (0 : ℚ) < certificate.sqrtEnclosure.lower := by
      simpa only [decide_eq_true_eq] using checks.sqrtPositive
    simpa [sqrtEnclosure, RationalEnclosure.SqrtCertificate.enclosure] using
      hpositive
  have hprobabilityPositive :
      (0 : ℚ) < certificate.lowerProbability.lower :=
    RationalEnclosure.LogRangeCertificate.input_pos_of_check
      checks.lowerLower
  rw [lowerProbability_lower_eq] at hprobabilityPositive
  have hrootUpperLt : certificate.sqrtOneSub.upper < 1 := by
    linarith
  have hrootLowerSq' :
      certificate.sqrtOneSub.lower ^ 2 ≤ 1 - y := by
    simpa [sqrtInput, RationalEnclosure.point] using hrootLowerSq
  have hrootUpperSq' :
      1 - y ≤ certificate.sqrtOneSub.upper ^ 2 := by
    simpa [sqrtInput, RationalEnclosure.point] using hrootUpperSq
  constructor
  · nlinarith
  · nlinarith [sq_pos_of_pos hrootLowerPositive]

end LRQPointCertificate
end CourtadeKumar
