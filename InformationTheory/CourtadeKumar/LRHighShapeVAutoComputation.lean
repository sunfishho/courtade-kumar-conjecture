import InformationTheory.CourtadeKumar.LRHighShapeMidpointEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantAutoQCertificate
import InformationTheory.CourtadeKumar.LRHighShapeCoordinateAutoCertificate

set_option autoImplicit false

/-!
# Executable payload generation shared by high-shape certificates

This module contains only the midpoint payload alias and deterministic,
untrusted proposal constructors.  The direct-`V` semantic evaluator and its
region assembly remain in `LRHighShapeVEvaluator`.
-/

namespace CourtadeKumar

/-- No new untrusted data are needed beyond the half-midpoint payload. -/
abbrev LRHighShapeVCertificate := LRHighShapeMidpointCertificate

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

end LRHighShapeVCertificate
end CourtadeKumar
