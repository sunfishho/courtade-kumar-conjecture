import InformationTheory.CourtadeKumar.LRDeterminantAutoQCertificateCorrectness
import InformationTheory.CourtadeKumar.LRCertificateOmegaZeroInterval

/-!
# Correctness of deterministic composite certificates

This layer assembles the Q-function correctness results into the omega and
logarithmic AD certificate checkers used by the upper-K evaluator.
-/

namespace CourtadeKumar

namespace LROmegaADCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ) (s y : IntervalAD) : Bool :=
  let b := lrCertificateBAD s y
  LRQADCertificate.autoSucceeds sqrtFuel logFuel b.value &&
    (LRQADCertificate.autoSucceeds sqrtFuel logFuel y.value &&
      LRQPrimeADCertificate.autoSucceeds sqrtFuel logFuel b.value)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (s y : IntervalAD)
    (hsucceeds : autoSucceeds sqrtFuel logFuel s y = true) :
    (auto sqrtFuel logFuel s y).check s y = true := by
  let b := lrCertificateBAD s y
  simp only [autoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [LROmegaADCertificate.check, LROmegaADCertificate.auto,
    LRQADCertificate.auto_check_of_succeeds _ _ _ hsucceeds.1,
    LRQADCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2.1,
    LRQPrimeADCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2.2]

end LROmegaADCertificate

namespace LROmegaZeroADCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ) (s : IntervalAD) : Bool :=
  LRQADCertificate.autoSucceeds sqrtFuel logFuel s.value &&
    LRQPrimeADCertificate.autoSucceeds sqrtFuel logFuel s.value

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ) (s : IntervalAD)
    (hsucceeds : autoSucceeds sqrtFuel logFuel s = true) :
    (auto sqrtFuel logFuel s).check s = true := by
  simp only [autoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [LROmegaZeroADCertificate.check, LROmegaZeroADCertificate.auto,
    LRQADCertificate.auto_check_of_succeeds _ _ _ hsucceeds.1,
    LRQPrimeADCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2]

end LROmegaZeroADCertificate

namespace LROmegaZeroIntervalCertificate

def autoSucceeds (sqrtFuel logFuel : ℕ) (s y : IntervalAD) : Bool :=
  let b := lrCertificateBAD s y
  LRQIntervalCertificate.autoSucceeds sqrtFuel logFuel b.value &&
    (LRQZeroIntervalCertificate.autoSucceeds y.value &&
      LRQPrimeIntervalCertificate.autoSucceeds sqrtFuel logFuel b.value)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (s y : IntervalAD)
    (hsucceeds : autoSucceeds sqrtFuel logFuel s y = true) :
    (auto sqrtFuel logFuel s y).check s y = true := by
  let b := lrCertificateBAD s y
  simp only [autoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [LROmegaZeroIntervalCertificate.check,
    LROmegaZeroIntervalCertificate.auto,
    LRQIntervalCertificate.auto_check_of_succeeds _ _ _ hsucceeds.1,
    LRQZeroIntervalCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2.1,
    LRQPrimeIntervalCertificate.auto_check_of_succeeds _ _ _ hsucceeds.2.2]

end LROmegaZeroIntervalCertificate

namespace LRG0ADCertificate

def autoSucceeds (logFuel : ℕ) (v : IntervalAD) : Bool :=
  RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel v.value &&
    (RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
        (onePlusV v).value &&
      RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
        (IntervalAD.const 2).value) &&
    decide ((0 : ℚ) < v.value.lower)

theorem auto_check_of_succeeds (logFuel : ℕ) (v : IntervalAD)
    (hsucceeds : autoSucceeds logFuel v = true) :
    (auto logFuel v).check v = true := by
  simp only [autoSucceeds, Bool.and_eq_true, decide_eq_true_eq]
    at hsucceeds
  simp only [LRG0ADCertificate.check, LRG0ADCertificate.auto,
    decide_eq_true_eq]
  exact ⟨
    RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel v.value hsucceeds.1.1,
    RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (onePlusV v).value hsucceeds.1.2.1,
    RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (IntervalAD.const 2).value hsucceeds.1.2.2,
    hsucceeds.2⟩

end LRG0ADCertificate

end CourtadeKumar
