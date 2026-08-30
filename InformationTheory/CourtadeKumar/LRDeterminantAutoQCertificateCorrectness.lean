import InformationTheory.CourtadeKumar.LRDeterminantAutoCertificateCorrectness

/-!
# Correctness of deterministic Q-function certificates

Small Boolean success predicates are connected to the original interval,
point, prime, and automatic-differentiation certificate checkers.
-/

namespace CourtadeKumar

namespace LRQPointCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ) (y : ℚ) : Bool :=
  let certificate := auto sqrtFuel logFuel y
  decide ((0 : ℚ) ≤ (sqrtInput y).lower ∧
      (sqrtInput y).lower ≤ (sqrtInput y).upper) &&
    (RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
        certificate.lowerProbability &&
      RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
        certificate.upperProbability)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ) (y : ℚ)
    (hsucceeds : autoSucceeds sqrtFuel logFuel y = true) :
    (auto sqrtFuel logFuel y).check y = true := by
  let certificate := auto sqrtFuel logFuel y
  have hparts :
      ((0 : ℚ) ≤ (sqrtInput y).lower ∧
        (sqrtInput y).lower ≤ (sqrtInput y).upper) ∧
      RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
          certificate.lowerProbability = true ∧
      RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
          certificate.upperProbability = true := by
    simpa [autoSucceeds, certificate, Bool.and_eq_true,
      decide_eq_true_eq] using hsucceeds
  have hsqrt : certificate.sqrtOneSub.check (sqrtInput y) = true := by
    change (RationalEnclosure.autoSqrtCertificate sqrtFuel
      (sqrtInput y)).check (sqrtInput y) = true
    exact RationalEnclosure.autoSqrtCertificate_check
      hparts.1.1 hparts.1.2 sqrtFuel
  have hlower : certificate.logLowerProbability.check
      certificate.lowerProbability = true := by
    change (RationalEnclosure.autoLogIntervalCertificate logFuel
      certificate.lowerProbability).check certificate.lowerProbability = true
    exact RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel certificate.lowerProbability hparts.2.1
  have hupper : certificate.logUpperProbability.check
      certificate.upperProbability = true := by
    change (RationalEnclosure.autoLogIntervalCertificate logFuel
      certificate.upperProbability).check certificate.upperProbability = true
    exact RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel certificate.upperProbability hparts.2.2
  simpa [LRQPointCertificate.check, certificate] using
    And.intro (And.intro hsqrt hlower) hupper

def autoPrimeSucceeds (sqrtFuel logFuel : ℕ) (y : ℚ) : Bool :=
  autoSucceeds sqrtFuel logFuel y &&
    decide ((0 : ℚ) < (auto sqrtFuel logFuel y).sqrtEnclosure.lower)

theorem auto_primeCheck_of_succeeds (sqrtFuel logFuel : ℕ) (y : ℚ)
    (hsucceeds : autoPrimeSucceeds sqrtFuel logFuel y = true) :
    (auto sqrtFuel logFuel y).primeCheck y = true := by
  simp only [autoPrimeSucceeds, Bool.and_eq_true, decide_eq_true_eq]
    at hsucceeds
  simpa [primeCheck, auto_check_of_succeeds _ _ _ hsucceeds.1]
    using hsucceeds.2

end LRQPointCertificate

namespace LRQIntervalCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure) : Bool :=
  decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1) &&
    (LRQPointCertificate.autoSucceeds sqrtFuel logFuel input.lower &&
      LRQPointCertificate.autoSucceeds sqrtFuel logFuel input.upper)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure)
    (hsucceeds : autoSucceeds sqrtFuel logFuel input = true) :
    (auto sqrtFuel logFuel input).check input = true := by
  simp only [autoSucceeds, Bool.and_eq_true, decide_eq_true_eq]
    at hsucceeds
  simp [LRQIntervalCertificate.check, LRQIntervalCertificate.auto,
    hsucceeds.1,
    LRQPointCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2.1,
    LRQPointCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2.2]

end LRQIntervalCertificate

namespace LRQZeroIntervalCertificate

def autoSucceeds (input : RationalEnclosure) : Bool :=
  decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
    input.upper < 1)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure)
    (hsucceeds : autoSucceeds input = true) :
    (auto sqrtFuel logFuel input).check input = true := by
  have hdomain : (0 : ℚ) ≤ input.lower ∧
      input.lower ≤ input.upper ∧ input.upper < 1 := by
    simpa [autoSucceeds] using hsucceeds
  simp only [LRQZeroIntervalCertificate.check,
    LRQZeroIntervalCertificate.auto, hdomain, decide_true, true_and]
  by_cases hzero : input.upper = 0
  · simp [hzero]
  · simp only [hzero, if_false]
    apply Bool.or_eq_true_iff.mpr
    right
    exact RationalEnclosure.autoSqrtCertificate_check
      (by simpa [RationalEnclosure.point] using hdomain.1.trans hdomain.2.1)
      (by simp [RationalEnclosure.point]) sqrtFuel

end LRQZeroIntervalCertificate

namespace LRQPrimeIntervalCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure) : Bool :=
  decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1) &&
    (LRQPointCertificate.autoPrimeSucceeds sqrtFuel logFuel input.lower &&
      LRQPointCertificate.autoPrimeSucceeds sqrtFuel logFuel input.upper)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure)
    (hsucceeds : autoSucceeds sqrtFuel logFuel input = true) :
    (auto sqrtFuel logFuel input).check input = true := by
  simp only [autoSucceeds, Bool.and_eq_true, decide_eq_true_eq]
    at hsucceeds
  simp [LRQPrimeIntervalCertificate.check, LRQPrimeIntervalCertificate.auto,
    hsucceeds.1,
    LRQPointCertificate.auto_primeCheck_of_succeeds _ _ _ hsucceeds.2.1,
    LRQPointCertificate.auto_primeCheck_of_succeeds _ _ _ hsucceeds.2.2]

end LRQPrimeIntervalCertificate

namespace LRQADCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure) : Bool :=
  LRQIntervalCertificate.autoSucceeds sqrtFuel logFuel input &&
    LRQPrimeIntervalCertificate.autoSucceeds sqrtFuel logFuel input

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure)
    (hsucceeds : autoSucceeds sqrtFuel logFuel input = true) :
    (auto sqrtFuel logFuel input).check input = true := by
  simp only [autoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [LRQADCertificate.check, LRQADCertificate.auto,
    LRQIntervalCertificate.auto_check_of_succeeds _ _ _ hsucceeds.1,
    LRQPrimeIntervalCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2]

end LRQADCertificate

namespace LRQPrimeADCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure) : Bool :=
  LRQPrimeIntervalCertificate.autoSucceeds sqrtFuel logFuel input &&
    lrQSecondCoarseCheck input

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure)
    (hsucceeds : autoSucceeds sqrtFuel logFuel input = true) :
    (auto sqrtFuel logFuel input).check input = true := by
  simp only [autoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [LRQPrimeADCertificate.check, LRQPrimeADCertificate.auto,
    LRQPrimeIntervalCertificate.auto_check_of_succeeds _ _ _ hsucceeds.1,
    hsucceeds.2]

end LRQPrimeADCertificate

end CourtadeKumar
