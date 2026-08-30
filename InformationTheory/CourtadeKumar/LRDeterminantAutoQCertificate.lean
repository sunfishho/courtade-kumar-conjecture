import InformationTheory.CourtadeKumar.LRDeterminantAutoCertificateCore
import InformationTheory.CourtadeKumar.LRCertificateQEnclosure
import InformationTheory.CourtadeKumar.LRCertificateQAD

/-!
# Lightweight deterministic Q-certificate constructors

This module assembles the elementary automatic payloads into the Q-specific
certificate records.  It deliberately has no dependency on the high-shape
evaluator, so Q point correctness can be imported by generated point proofs
without loading that evaluator.
-/

namespace CourtadeKumar

namespace LRQPointCertificate

def auto (sqrtFuel logFuel : ℕ) (y : ℚ) : LRQPointCertificate :=
  let sqrtOneSub := RationalEnclosure.autoSqrtCertificate sqrtFuel
    (sqrtInput y)
  let seed : LRQPointCertificate :=
    { sqrtOneSub := sqrtOneSub
      logLowerProbability :=
        { lower := { exponent := 0, mantissa := 0 }
          upper := { exponent := 0, mantissa := 0 } }
      logUpperProbability :=
        { lower := { exponent := 0, mantissa := 0 }
          upper := { exponent := 0, mantissa := 0 } } }
  { sqrtOneSub := sqrtOneSub
    logLowerProbability :=
      RationalEnclosure.autoLogIntervalCertificate logFuel
        seed.lowerProbability
    logUpperProbability :=
      RationalEnclosure.autoLogIntervalCertificate logFuel
        seed.upperProbability }

end LRQPointCertificate

namespace LRQIntervalCertificate

def auto (sqrtFuel logFuel : ℕ) (input : RationalEnclosure) :
    LRQIntervalCertificate :=
  { lower := LRQPointCertificate.auto sqrtFuel logFuel input.lower
    upper := LRQPointCertificate.auto sqrtFuel logFuel input.upper }

end LRQIntervalCertificate

namespace LRQZeroIntervalCertificate

def auto (sqrtFuel logFuel : ℕ) (input : RationalEnclosure) :
    LRQZeroIntervalCertificate :=
  { upper := LRQPointCertificate.auto sqrtFuel logFuel input.upper
    sqrtUpper := RationalEnclosure.autoSqrtCertificate sqrtFuel
      (RationalEnclosure.point input.upper) }

end LRQZeroIntervalCertificate

namespace LRQPrimeIntervalCertificate

def auto (sqrtFuel logFuel : ℕ) (input : RationalEnclosure) :
    LRQPrimeIntervalCertificate :=
  { lowerEndpoint := LRQPointCertificate.auto sqrtFuel logFuel input.lower
    upperEndpoint := LRQPointCertificate.auto sqrtFuel logFuel input.upper }

end LRQPrimeIntervalCertificate

namespace LRQADCertificate

def auto (sqrtFuel logFuel : ℕ) (input : RationalEnclosure) :
    LRQADCertificate :=
  { value := LRQIntervalCertificate.auto sqrtFuel logFuel input
    slope := LRQPrimeIntervalCertificate.auto sqrtFuel logFuel input }

end LRQADCertificate

namespace LRQPrimeADCertificate

def auto (sqrtFuel logFuel : ℕ) (input : RationalEnclosure) :
    LRQPrimeADCertificate :=
  { value := LRQPrimeIntervalCertificate.auto sqrtFuel logFuel input }

end LRQPrimeADCertificate

end CourtadeKumar
