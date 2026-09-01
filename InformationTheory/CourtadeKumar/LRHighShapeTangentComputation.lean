import InformationTheory.CourtadeKumar.LRHighShapeMidpointEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeVAutoComputation

set_option autoImplicit false

/-!
# Executable arithmetic for the high-shape tangent certificate

This module contains the untrusted tangent payload, its interval-AD
evaluation and Boolean checker, and deterministic payload generation.
Real-valued soundness and subdivision-tree assembly remain in their existing
semantic modules.
-/

namespace CourtadeKumar

structure LRHighShapeTangentCertificate where
  base : LRHighShapeMidpointCertificate
  qBY0 : LRQADCertificate
  qBE : LRQADCertificate
  qS : LRQADCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate

namespace LRHighShapeTangentCertificate

structure Evaluation where
  target : IntervalAD
  squareTarget : IntervalAD
  prefixAtM : IntervalAD
  gap : IntervalAD
  halfSlope : IntervalAD
  j : IntervalAD
  midpointNumerator : IntervalAD

def evaluateAll (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Evaluation :=
  let coordinate := certificate.base.kernel.coordinate
  let v := coordinate.vAD box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let x := lrCertificateXAD box
  let y0 := lrCertificateY0AD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  let qBY0 := certificate.qBY0.evaluate terms by0
  let qBE := certificate.qBE.evaluate terms be
  let qS := certificate.qS.evaluate terms s
  let g0 := certificate.base.gShape.g0.evaluate terms v
  let logTwo := IntervalAD.log terms certificate.base.gShape.g0.logTwo
    (IntervalAD.const 2)
  let logOnePlusV := IntervalAD.log terms certificate.base.ab.logOnePlusV
    (IntervalAD.add (IntervalAD.const 1) v)
  let logTwoPlusV := IntervalAD.log terms certificate.logTwoPlusV
    (IntervalAD.add (IntervalAD.const 2) v)
  let squareTarget := IntervalAD.add (IntervalAD.add g0 qBY0)
    (IntervalAD.divPositive qBE v)
  let core := IntervalAD.add g0
    (IntervalAD.mul
      (IntervalAD.add (IntervalAD.const 1) (IntervalAD.invPositive v))
      logTwo)
  let delta := IntervalAD.sub qS (IntervalAD.mul s logTwo)
  let prefixAtM := IntervalAD.add (IntervalAD.mul s core)
    (IntervalAD.divPositive (IntervalAD.mul (IntervalAD.const 4) delta)
      (IntervalAD.add (IntervalAD.const 1) v))
  let gap := IntervalAD.sub squareTarget prefixAtM
  let logFactor := IntervalAD.sub (IntervalAD.add logTwo logOnePlusV)
    logTwoPlusV
  let onePlusVSq := IntervalAD.mul
    (IntervalAD.add (IntervalAD.const 1) v)
    (IntervalAD.add (IntervalAD.const 1) v)
  let vSq := IntervalAD.mul v v
  let ratio := IntervalAD.divPositive
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) s)
      onePlusVSq)
    vSq
  let halfSlope := IntervalAD.add (IntervalAD.mul ratio logFactor)
    (IntervalAD.mul (IntervalAD.const 4) delta)
  let ab := certificate.base.ab.evaluate terms box coordinate
  let g := certificate.base.gShape.evaluate terms box coordinate
  let w := certificate.base.kernel.wAD terms box
  let pw := certificate.base.kernel.pwAD terms box
  let m := certificate.base.mAD box
  let j := IntervalAD.sub (IntervalAD.mul ab.b x) ab.d
  let bracket := IntervalAD.add
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) m) ab.d)
    (IntervalAD.mul (IntervalAD.mul m x) ab.b)
  let midpointNumerator := IntervalAD.sub
    (IntervalAD.add (IntervalAD.mul ab.d g) (IntervalAD.mul ab.a pw))
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) bracket)
  let target := IntervalAD.add
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) j) gap)
    (IntervalAD.mul halfSlope midpointNumerator)
  { target := target
    squareTarget := squareTarget
    prefixAtM := prefixAtM
    gap := gap
    halfSlope := halfSlope
    j := j
    midpointNumerator := midpointNumerator }

def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : IntervalAD :=
  (certificate.evaluateAll terms box).target

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : MidpointCertificate :=
  let result := certificate.evaluateAD terms box
  { value := result.value
    derivS := result.derivS
    derivK := result.derivK
    derivChi := result.derivChi }

def check (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Bool :=
  let coordinate := certificate.base.kernel.coordinate
  let v := coordinate.vAD box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  decide (
    certificate.base.check box = true ∧
    certificate.qBY0.check by0.value = true ∧
    certificate.qBE.check be.value = true ∧
    certificate.qS.check s.value = true ∧
    certificate.logTwoPlusV.check
      (IntervalAD.add (IntervalAD.const 2) v).value = true ∧
    (0 : ℚ) < v.value.lower ∧
    (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
    (0 : ℚ) < (IntervalAD.add (IntervalAD.const 2) v).value.lower ∧
    (0 : ℚ) < (IntervalAD.mul v v).value.lower)

def payloadCheck (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Bool :=
  lrHighShapeInteriorBoxCheck box && certificate.check box

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Bool :=
  checkedMidpointLeafAccepts payloadCheck (evaluate terms) box certificate

/-- Generate every square-root and logarithm proposal used by one tangent
leaf. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRHighShapeTangentCertificate :=
  let base := LRHighShapeVCertificate.auto sqrtFuel logFuel box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let v := base.kernel.coordinate.vAD box
  { base := base
    qBY0 := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateBAD s y0).value
    qBE := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateBAD s e).value
    qS := LRQADCertificate.auto sqrtFuel logFuel s.value
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.add (IntervalAD.const 2) v).value }

end LRHighShapeTangentCertificate
end CourtadeKumar
