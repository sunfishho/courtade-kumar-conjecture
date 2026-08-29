import InformationTheory.CourtadeKumar.LRCertificateQSharpSecondEnclosure
import InformationTheory.CourtadeKumar.LRCertificateQRegularizedScale
import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator

/-!
# Executable historical sharp `A/C` nodes for the upper-`K` replay

This module contains the interval definitions and Boolean-check plumbing for
the historical sharp `A/C` nodes.  Corner-value soundness is established in a
separate module.

The historical derivative ledger uses, for `y = y0` and
`b = s + (1-s)y`,

* `Areg = y * Q'(y)` and `Breg = sqrt(y) * Q'(y)`;
* `q_s = 2*Areg/s`, `q_K = Areg/K`,
  `q_h = 2*sqrt(e)*Breg`;
* `C_s^0 = s*(Q''(s) - (1-y)^2*Q''(b))`;
* `M = Q'(b) - s*(1-s)*(1-y)*Q''(b)`.

Writing `y_s = 2y/s`, `y_K = y/K`, and `y_h = 2he`, the composite
partials are

* `A_* = (C_s^0 + M*y_s, M*y_K, M*y_h)`;
* `C_* = (C_s^0 + M*y_s - q_s, M*y_K - q_K, M*y_h - q_h)`.

Only after those derivative intervals are formed do we attach the already
verified production value projection.  This separation prevents any hidden
assumption that an `A` or `C` value is monotone and hence determined by
corners.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalACAD

open LRUpperKReplayCertificate

/-! ## Payload and checks -/

/-- Extra untrusted endpoint data beyond the production replay payload.

The production `qY0` certificate already supplies the positive upper
endpoint data.  Thus the sharp regularized certificate adds only the lower
`Q'` endpoint and lower `sqrt(y0)` endpoint.  A separate certificate encloses
`sqrt(e)` for the regularized `h` partial. -/
structure Payload where
  base : LRUpperKReplayCertificate.Payload
  qY0LowerPrime : LRQPointCertificate
  qY0SqrtLower : RationalEnclosure.SqrtCertificate
  sqrtE : RationalEnclosure.SqrtCertificate

/-- Repackage the existing production `qY0` upper data together with the
two new lower-endpoint fields. -/
def qY0ScaleCertificate (payload : Payload) :
    LRQRegularizedScaleCertificate :=
  { toLRQZeroIntervalCertificate := payload.base.qY0
    lower := payload.qY0LowerPrime
    sqrtLower := payload.qY0SqrtLower }

/-- Checks used only by the new sharp scalar nodes.

The final two conjuncts are deliberately direct checks of the existing
`Q'` interval payloads.  They make the dependencies of the sharp `Q''`
identity explicit instead of relying on projections from the larger base
checker. -/
def auxiliaryCheck (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  (qY0ScaleCertificate payload).check terms (y0AD box).value &&
    payload.sqrtE.check (eAD box).value &&
    payload.base.omegaZero.qPrimeAtS.value.check (sAD box).value &&
    payload.base.omegaY0.qPrimeAtB.check (y0BAd box).value

/-- Full executable checker: the production payload remains intact and the
new endpoint data are checked separately. -/
def check (terms : ℕ) (box : CertificateBox) (payload : Payload) : Bool :=
  LRUpperKReplayCertificate.payloadCheck box payload.base &&
    auxiliaryCheck terms box payload

/-! ## Small exact interval combinators -/

def mulNN (a b : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative a b

def mulNN3 (a b c : RationalEnclosure) : RationalEnclosure :=
  mulNN (mulNN a b) c

def squareNN (a : RationalEnclosure) : RationalEnclosure :=
  mulNN a a

/-- Intersect an interval's upper side with the analytic sign bound `x ≤ 0`.

For the historical `C_s^0` node, soundness of this refinement requires the
separate analytic lemma `C_s^0 ≤ 0`; it is not inferred from interval
endpoints here.  The unclamped interval is retained below as
`fixedYPartialSRawI`. -/
def capUpperZero (a : RationalEnclosure) : RationalEnclosure :=
  ⟨a.lower, min a.upper 0⟩

/-! ## Sharp regularized `Q(y0)` partial scales -/

def y0MulPrimeI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (qY0ScaleCertificate payload).mulPrimeEnclosure terms (y0AD box).value

def y0SqrtMulPrimeI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (qY0ScaleCertificate payload).sqrtMulPrimeEnclosure terms (y0AD box).value

/-- `q_s = 2*(y0*Q'(y0))/s`. -/
def qPartialSI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.scale 2 (y0MulPrimeI terms box payload))
    (sAD box).value

/-- `q_K = (y0*Q'(y0))/K`. -/
def qPartialKI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.div (y0MulPrimeI terms box payload)
    (ratioAD box).value

/-- Checked enclosure of `sqrt(e)`. -/
def sqrtEI (payload : Payload) : RationalEnclosure :=
  payload.sqrtE.enclosure

/-- `q_h = 2*sqrt(e)*(sqrt(y0)*Q'(y0))`.

All factors are checked nonnegative by `auxiliaryCheck`, so the sharp
nonnegative product is the exact historical interval operation. -/
def qPartialHI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  mulNN3 (RationalEnclosure.point 2) (sqrtEI payload)
    (y0SqrtMulPrimeI terms box payload)

/-! ## Exact chart partials of `y0 = s^2*K*h^2` -/

def yPartialSI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.scale 2 (y0AD box).value) (sAD box).value

def yPartialKI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.div (y0AD box).value (ratioAD box).value

def yPartialHI (box : CertificateBox) : RationalEnclosure :=
  mulNN3 (RationalEnclosure.point 2) (hAD box).value (eAD box).value

/-! ## Tight `Q''` nodes at `s` and `b = s + (1-s)y0` -/

/-- Cancellation-aware `Q''(s)` enclosure, reusing the `Q'` interval already
present in `omegaZero.qPrimeAtS`. -/
def qSecondAtSI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  LRQSharpSecondEnclosure.enclosure terms (sAD box).value
    payload.base.omegaZero.qPrimeAtS.value

/-- Cancellation-aware `Q''(b)` enclosure, reusing the `Q'` interval already
present in `omegaY0.qPrimeAtB`. -/
def qSecondAtBI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  LRQSharpSecondEnclosure.enclosure terms (y0BAd box).value
    payload.base.omegaY0.qPrimeAtB

def oneMinusYI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1) (y0AD box).value

def oneMinusSI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1) (sAD box).value

/-- Raw interval arithmetic for
`s*(Q''(s) - (1-y0)^2*Q''(b))`. -/
def fixedYPartialSRawI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.mul (sAD box).value
    (RationalEnclosure.sub (qSecondAtSI terms box payload)
      (RationalEnclosure.mul (squareNN (oneMinusYI box))
        (qSecondAtBI terms box payload)))

/-- Historical refinement of `fixedYPartialSRawI` by the analytic upper
bound `C_s^0 ≤ 0`. -/
def fixedYPartialSI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  capUpperZero (fixedYPartialSRawI terms box payload)

/-- `M = Q'(b) - s*(1-s)*(1-y0)*Q''(b)`. -/
def movingYCoefficientI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let nonnegativeFactor :=
    mulNN3 (sAD box).value (oneMinusSI box) (oneMinusYI box)
  RationalEnclosure.sub
    (payload.base.omegaY0.qPrimeAtB.enclosure terms)
    (RationalEnclosure.mul nonnegativeFactor
      (qSecondAtBI terms box payload))

/-! ## Derivative-only historical `A/C` composites -/

/-- Three chart-partial enclosures.  `derivH` corresponds to the third
`IntervalAD.derivChi` field because the upper-`K` chart stores `h` there. -/
structure Partials where
  derivS : RationalEnclosure
  derivK : RationalEnclosure
  derivH : RationalEnclosure

/-- Faithful historical composite partials for `A(y0)`.

No value interval is attached here. -/
def aY0Partials (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Partials :=
  let cs := fixedYPartialSI terms box payload
  let m := movingYCoefficientI terms box payload
  { derivS := RationalEnclosure.add cs
      (RationalEnclosure.mul m (yPartialSI box))
    derivK := RationalEnclosure.mul m (yPartialKI box)
    derivH := RationalEnclosure.mul m (yPartialHI box) }

/-- Faithful historical composite partials for `C(y0) = A(y0)-Q(y0)`.

The three regularized `Q` partials are subtracted componentwise, including
the finite `h=0` continuation supplied by `sqrt(y0)*Q'(y0)`. -/
def cY0Partials (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Partials :=
  let a := aY0Partials terms box payload
  { derivS := RationalEnclosure.sub a.derivS
      (qPartialSI terms box payload)
    derivK := RationalEnclosure.sub a.derivK
      (qPartialKI terms box payload)
    derivH := RationalEnclosure.sub a.derivH
      (qPartialHI terms box payload) }

/-! ## Value projection, deliberately separate from derivative construction -/

/-- Production whole-box value enclosure for `A(y0)`.  This is not a
monotone-corner projection; it is the value field of the already assembled
interval expression. -/
def aY0ValueI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (LRUpperKReplayCertificate.aY0SKAD terms box payload.base).value

/-- Production whole-box value enclosure for `C(y0)`. -/
def cY0ValueI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (LRUpperKReplayCertificate.cY0SKAD terms box payload.base).value

/-- Convenience assembly for downstream replay experiments.  Its value and
derivative components come from independently identified soundness
obligations; this definition itself asserts no semantic theorem. -/
def aY0ProjectedAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let partials := aY0Partials terms box payload
  { value := aY0ValueI terms box payload
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-- Convenience assembly for the historical `C(y0)` node, with the same
separation of the production value enclosure from the sharp partials. -/
def cY0ProjectedAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let partials := cY0Partials terms box payload
  { value := cY0ValueI terms box payload
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-! ## The same historical composite at `y = e = s^2*K` -/

def qSecondAtEBI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  LRQSharpSecondEnclosure.enclosure terms (eBAd box).value
    payload.base.omegaE.qPrimeAtB.value

def oneMinusEI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1) (eAD box).value

def ePartialSI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.scale 2 (eAD box).value) (sAD box).value

def ePartialKI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.div (eAD box).value (ratioAD box).value

def fixedEPartialSRawI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.mul (sAD box).value
    (RationalEnclosure.sub (qSecondAtSI terms box payload)
      (RationalEnclosure.mul (squareNN (oneMinusEI box))
        (qSecondAtEBI terms box payload)))

def fixedEPartialSI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  capUpperZero (fixedEPartialSRawI terms box payload)

def movingECoefficientI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let nonnegativeFactor :=
    mulNN3 (sAD box).value (oneMinusSI box) (oneMinusEI box)
  RationalEnclosure.sub
    (payload.base.omegaE.qPrimeAtB.value.enclosure terms)
    (RationalEnclosure.mul nonnegativeFactor
      (qSecondAtEBI terms box payload))

def qPrimeEI (terms : ℕ) (payload : Payload) : RationalEnclosure :=
  payload.base.omegaE.qAtY.slope.enclosure terms

def aEPartials (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Partials :=
  let cs := fixedEPartialSI terms box payload
  let m := movingECoefficientI terms box payload
  { derivS := RationalEnclosure.add cs
      (RationalEnclosure.mul m (ePartialSI box))
    derivK := RationalEnclosure.mul m (ePartialKI box)
    derivH := RationalEnclosure.point 0 }

def cEPartials (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Partials :=
  let a := aEPartials terms box payload
  let qPrime := qPrimeEI terms payload
  { derivS := RationalEnclosure.sub a.derivS
      (RationalEnclosure.mul qPrime (ePartialSI box))
    derivK := RationalEnclosure.sub a.derivK
      (RationalEnclosure.mul qPrime (ePartialKI box))
    derivH := RationalEnclosure.point 0 }

def aEProjectedAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let partials := aEPartials terms box payload
  { value := (LRUpperKReplayCertificate.aESKAD terms box payload.base).value
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def cEProjectedAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let partials := cEPartials terms box payload
  { value := (LRUpperKReplayCertificate.cESKAD terms box payload.base).value
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

/-!
## Remaining semantic obligations for integration

No declarations are introduced for these yet.

1. Extract the four new check facts from `check = true` and apply
   `LRQRegularizedScaleCertificate.mulPrime_sound`,
   `LRQRegularizedScaleCertificate.sqrtMulPrime_sound`, the square-root
   certificate soundness theorem, and both
   `LRQSecondPointEnclosure.intervalEnclosure_sound` instances.
2. Prove the analytic sign bound
   `s*(Q''(s) - (1-y)^2*Q''(s+(1-s)y)) ≤ 0` on the physical domain.  This
   alone justifies `capUpperZero`; `fixedYPartialSRawI` needs no such lemma.
3. Prove the algebraic chain-rule identities encoded by `aY0Partials` and
   `cY0Partials`, including the exact `h=0` continuation of `q_h`.
4. Combine those derivative results with the existing production value
   soundness of `aY0SKAD` and `cY0SKAD`.  No monotone-corner value theorem is
   needed or used by this draft.
-/

end LRUpperKHistoricalACAD
end CourtadeKumar
