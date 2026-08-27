import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator

/-!
# Deterministic payload generation for high-shape `V` leaves

These functions merely propose rational square-root and logarithm payloads.
They are outside the trusted semantic argument: every generated field is
subsequently validated by the existing executable certificate checkers.
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
  { upper := LRQPointCertificate.auto sqrtFuel logFuel input.upper }

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

namespace LROmegaADCertificate

def auto (sqrtFuel logFuel : ℕ) (s y : IntervalAD) :
    LROmegaADCertificate :=
  let b := lrCertificateBAD s y
  { qAtB := LRQADCertificate.auto sqrtFuel logFuel b.value
    qAtY := LRQADCertificate.auto sqrtFuel logFuel y.value
    qPrimeAtB := LRQPrimeADCertificate.auto sqrtFuel logFuel b.value }

end LROmegaADCertificate

namespace LROmegaZeroADCertificate

def auto (sqrtFuel logFuel : ℕ) (s : IntervalAD) :
    LROmegaZeroADCertificate :=
  { qAtS := LRQADCertificate.auto sqrtFuel logFuel s.value
    qPrimeAtS := LRQPrimeADCertificate.auto sqrtFuel logFuel s.value }

end LROmegaZeroADCertificate

namespace LRHighShapeCoordinateCertificate

def auto (sqrtFuel : ℕ) (box : CertificateBox) :
    LRHighShapeCoordinateCertificate :=
  { tSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
      (lrCertificateXAD box).value
    vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
      (lrCertificateVRadicandAD box).value }

end LRHighShapeCoordinateCertificate

namespace LRHighShapeKernelCertificate

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRHighShapeKernelCertificate :=
  let s := lrCertificateSAD box
  let coordinate := LRHighShapeCoordinateCertificate.auto sqrtFuel box
  { coordinate := coordinate
    omegaZero := LROmegaZeroADCertificate.auto sqrtFuel logFuel s
    omegaY0 := LROmegaADCertificate.auto sqrtFuel logFuel s
      (lrCertificateY0AD box)
    omegaE := LROmegaADCertificate.auto sqrtFuel logFuel s
      (lrCertificateEAD box) }

end LRHighShapeKernelCertificate

namespace LRG0ADCertificate

def auto (logFuel : ℕ) (v : IntervalAD) : LRG0ADCertificate :=
  { logV := RationalEnclosure.autoLogIntervalCertificate logFuel v.value
    logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (onePlusV v).value
    logTwo := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.const 2).value }

end LRG0ADCertificate

namespace LRHighShapeGCertificate

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (coordinate : LRHighShapeCoordinateCertificate) :
    LRHighShapeGCertificate :=
  let v := coordinate.vAD box
  { g0 := LRG0ADCertificate.auto logFuel v
    qY0 := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateY0AD box).value
    qE := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateEAD box).value }

end LRHighShapeGCertificate

namespace LRHighShapeABCertificate

def auto (logFuel : ℕ) (box : CertificateBox)
    (coordinate : LRHighShapeCoordinateCertificate) :
    LRHighShapeABCertificate :=
  let v := coordinate.vAD box
  let e := lrCertificateEAD box
  let be := lrCertificateBAD (lrCertificateSAD box) e
  { logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.add (IntervalAD.const 1) v).value
    logE := RationalEnclosure.autoLogIntervalCertificate logFuel e.value
    logBE := RationalEnclosure.autoLogIntervalCertificate logFuel be.value }

end LRHighShapeABCertificate

namespace LRHighShapeVCertificate

/-- Generate the complete checked payload from the current leaf box. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRHighShapeVCertificate :=
  let kernel := LRHighShapeKernelCertificate.auto sqrtFuel logFuel box
  { kernel := kernel
    gShape := LRHighShapeGCertificate.auto sqrtFuel logFuel box
      kernel.coordinate
    ab := LRHighShapeABCertificate.auto logFuel box kernel.coordinate }

/-- Acceptance with a generated payload; the unit argument lets this be used
with the generic subdivision datatype without storing payload records. -/
def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  accepts terms box (auto sqrtFuel logFuel box)

end LRHighShapeVCertificate

end CourtadeKumar
