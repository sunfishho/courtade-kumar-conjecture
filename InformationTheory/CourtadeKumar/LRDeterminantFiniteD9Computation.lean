import InformationTheory.CourtadeKumar.LRHighShapeTangentComputation

set_option autoImplicit false

/-!
# Executable arithmetic for the regular finite-D9 evaluator

This module contains only the untrusted payload type, its exact interval-AD
evaluation, the Boolean payload checker, and deterministic proposal
generation.  Semantic soundness and the raw-tree adapters remain in
`LRDeterminantFiniteD9Evaluator`.
-/

namespace CourtadeKumar

/-- Untrusted scalar data for a direct D9 enclosure.  All fields are checked
by executable Boolean predicates before their semantic theorems are used. -/
structure LRFiniteDeterminantD9Certificate where
  tangent : LRHighShapeTangentCertificate
  logD1Mean : RationalEnclosure.LogIntervalCertificate

namespace LRFiniteDeterminantD9Certificate

def yAD (box : CertificateBox) : IntervalAD :=
  let k := lrCertificateKAD box
  let e := lrCertificateEAD box
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.add (IntervalAD.const 1) k) e) k

def d1MeanAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul
    (IntervalAD.add (IntervalAD.const 1) (yAD box))
    (IntervalAD.const (1 / 2))

def d1DenominatorAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.mul (IntervalAD.const 3) (yAD box))
    (IntervalAD.const 1)

def d1AD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let y := yAD box
  let logMean := IntervalAD.log terms certificate.logD1Mean (d1MeanAD box)
  IntervalAD.add
    (IntervalAD.mul (IntervalAD.const (1 / 2)) logMean)
    (IntervalAD.divPositive
      (IntervalAD.sub y (IntervalAD.const 1))
      (d1DenominatorAD box))

def onePlusVAD (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1)
    (certificate.tangent.base.kernel.coordinate.vAD box)

/-- The exact cancellation-coordinate formula
`Psi = G + P_W - 4 W / (1 + v)`. -/
def psiAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let base := certificate.tangent.base
  let coordinate := base.kernel.coordinate
  let g := base.gShape.evaluate terms box coordinate
  let pw := base.kernel.pwAD terms box
  let w := base.kernel.wAD terms box
  IntervalAD.sub (IntervalAD.add g pw)
    (IntervalAD.divPositive
      (IntervalAD.mul (IntervalAD.const 4) w)
      (onePlusVAD box certificate))

/-- The exact coefficient `delta = (1 - v*x) / (1 + v)`. -/
def deltaAD (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let v := certificate.tangent.base.kernel.coordinate.vAD box
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.const 1)
      (IntervalAD.mul v (lrCertificateXAD box)))
    (onePlusVAD box certificate)

def firstBracketAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let base := certificate.tangent.base
  let coordinate := base.kernel.coordinate
  let b := (base.ab.evaluate terms box coordinate).b
  let g := base.gShape.evaluate terms box coordinate
  let w := base.kernel.wAD terms box
  let psi := psiAD terms box certificate
  let d1 := d1AD terms box certificate
  let delta := deltaAD box certificate
  IntervalAD.add
    (IntervalAD.mul b
      (IntervalAD.add (IntervalAD.sub psi g)
        (IntervalAD.mul
          (IntervalAD.mul (IntervalAD.const 4) delta) w)))
    (IntervalAD.mul d1 psi)

/-- Direct interval-AD extension of D9.  It retains `s*Hd` as the already
computed half-slope and `R*T` as the already computed gap. -/
def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let tangentValues := certificate.tangent.evaluateAll terms box
  let base := certificate.tangent.base
  let coordinate := base.kernel.coordinate
  let b := (base.ab.evaluate terms box coordinate).b
  let w := base.kernel.wAD terms box
  let d1 := d1AD terms box certificate
  let first := firstBracketAD terms box certificate
  let factor := IntervalAD.sub
    (IntervalAD.mul b (lrCertificateXAD box)) d1
  IntervalAD.add
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.const 3) tangentValues.halfSlope) first)
    (IntervalAD.mul
      (IntervalAD.mul
        (IntervalAD.mul (IntervalAD.const 4) w) tangentValues.gap)
      factor)

def enclose (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : RationalEnclosure :=
  (certificate.evaluateAD terms box).value

/-- This checker does not require the whole closed leaf to lie in the open
chi chart.  Positivity of `s`, `k`, `R`, the D1 denominator, and `1+v` is
instead checked directly on the rational enclosures.  Its reused `Q` AD
payload may still fail closed at `chi = 0`. -/
def payloadCheck (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : Bool :=
  decide (
    certificate.tangent.check box = true ∧
    (0 : ℚ) < (lrCertificateSAD box).value.lower ∧
    (0 : ℚ) < (lrCertificateKAD box).value.lower ∧
    (0 : ℚ) < (lrCertificateRAD box).value.lower ∧
    certificate.logD1Mean.check (d1MeanAD box).value = true ∧
    (0 : ℚ) < (d1DenominatorAD box).value.lower ∧
    (0 : ℚ) < (onePlusVAD box certificate).value.lower)

/-- Deterministically propose the full payload for one raw-coordinate leaf.
Proposal generation is untrusted; `payloadCheck` validates every field. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRFiniteDeterminantD9Certificate :=
  let tangent := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
  { tangent := tangent
    logD1Mean := RationalEnclosure.autoLogIntervalCertificate logFuel
      (d1MeanAD box).value }

end LRFiniteDeterminantD9Certificate
end CourtadeKumar
