import InformationTheory.CourtadeKumar.LRDeterminantAutoQCertificateCorrectness
import InformationTheory.CourtadeKumar.LRCertificateQRegularizedScale

/-!
# Correctness of the deterministic regularized-scale certificate

The constructor reuses deterministic Q and square-root certificates.  A
shallow success predicate is proved sufficient for the original checker.
-/

namespace CourtadeKumar
namespace LRQRegularizedScaleCertificate

def auto (sqrtFuel logFuel : ℕ) (input : RationalEnclosure) :
    LRQRegularizedScaleCertificate :=
  { toLRQZeroIntervalCertificate :=
      LRQZeroIntervalCertificate.auto sqrtFuel logFuel input
    lower := LRQPointCertificate.auto sqrtFuel logFuel input.lower
    sqrtLower := RationalEnclosure.autoSqrtCertificate sqrtFuel
      (RationalEnclosure.point input.lower) }

def endpointAutoSucceeds (terms sqrtFuel logFuel : ℕ) (y : ℚ) : Bool :=
  LRQPointCertificate.autoPrimeSucceeds sqrtFuel logFuel y &&
    decide ((0 : ℚ) ≤
      ((LRQPointCertificate.auto sqrtFuel logFuel y).primeEnclosure terms).lower)

theorem endpointAutoCheck_of_succeeds
    (terms sqrtFuel logFuel : ℕ) (y : ℚ) (hy : 0 ≤ y)
    (hsucceeds : endpointAutoSucceeds terms sqrtFuel logFuel y = true) :
    endpointCheck terms y
      (LRQPointCertificate.auto sqrtFuel logFuel y)
      (RationalEnclosure.autoSqrtCertificate sqrtFuel
        (RationalEnclosure.point y)) = true := by
  simp only [endpointAutoSucceeds, Bool.and_eq_true, decide_eq_true_eq]
    at hsucceeds
  have hprime := LRQPointCertificate.auto_primeCheck_of_succeeds
    sqrtFuel logFuel y hsucceeds.1
  have hyPointLower : (0 : ℚ) ≤ (RationalEnclosure.point y).lower := by
    exact hy
  have hyPointOrdered :
      (RationalEnclosure.point y).lower ≤
        (RationalEnclosure.point y).upper := by
    exact le_rfl
  have hsqrt := RationalEnclosure.autoSqrtCertificate_check
    (input := RationalEnclosure.point y)
    hyPointLower hyPointOrdered sqrtFuel
  simp [endpointCheck, hprime, hsqrt, hsucceeds.2]

def autoSucceeds (terms sqrtFuel logFuel : ℕ)
    (input : RationalEnclosure) : Bool :=
  decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1) &&
    if input.upper = 0 then true
    else endpointAutoSucceeds terms sqrtFuel logFuel input.upper &&
      if input.lower = 0 then true
      else endpointAutoSucceeds terms sqrtFuel logFuel input.lower

theorem auto_check_of_succeeds
    (terms sqrtFuel logFuel : ℕ) (input : RationalEnclosure)
    (hsucceeds : autoSucceeds terms sqrtFuel logFuel input = true) :
    (auto sqrtFuel logFuel input).check terms input = true := by
  have hparts :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
        input.upper < 1) = true ∧
      (if input.upper = 0 then true
        else endpointAutoSucceeds terms sqrtFuel logFuel input.upper &&
          if input.lower = 0 then true
          else endpointAutoSucceeds terms sqrtFuel logFuel input.lower) = true := by
    simpa [autoSucceeds] using hsucceeds
  have hdomain : (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1 := by
    simpa using hparts.1
  simp only [LRQRegularizedScaleCertificate.check, auto,
    LRQZeroIntervalCertificate.auto, hdomain, decide_true, true_and]
  by_cases hupperZero : input.upper = 0
  · simp [hupperZero]
  · have hupperPositive : (0 : ℚ) < input.upper :=
      lt_of_le_of_ne (hdomain.1.trans hdomain.2.1) (Ne.symm hupperZero)
    have hrest :
        endpointAutoSucceeds terms sqrtFuel logFuel input.upper = true ∧
        (if input.lower = 0 then true
          else endpointAutoSucceeds terms sqrtFuel logFuel input.lower) = true := by
      simpa [hupperZero] using hparts.2
    have hupper := endpointAutoCheck_of_succeeds
      terms sqrtFuel logFuel input.upper hupperPositive.le hrest.1
    simp only [hupperZero, if_false]
    by_cases hlowerZero : input.lower = 0
    · simpa [hlowerZero] using hupper
    · have hlowerPositive : (0 : ℚ) < input.lower :=
        lt_of_le_of_ne hdomain.1 (Ne.symm hlowerZero)
      have hlowerSuccess :
          endpointAutoSucceeds terms sqrtFuel logFuel input.lower = true := by
        simpa [hlowerZero] using hrest.2
      have hlower := endpointAutoCheck_of_succeeds
        terms sqrtFuel logFuel input.lower hlowerPositive.le hlowerSuccess
      simp [hlowerZero, hupper, hlower]

end LRQRegularizedScaleCertificate
end CourtadeKumar
