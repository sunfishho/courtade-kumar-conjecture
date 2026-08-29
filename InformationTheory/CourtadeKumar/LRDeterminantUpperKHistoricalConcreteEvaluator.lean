import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalEvaluatorAssembly
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalOpenMidpointLeaf

/-!
# Concrete centered checker for the historical upper-K replay

The compact tree stores no analytic payload.  Each leaf deterministically
reconstructs the exact point, interval, square-root, and logarithm
certificates checked by the semantic modules.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalConcreteEvaluator

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD
open LRUpperKHistoricalACValues
open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKHistoricalEvaluatorAssembly

def autoPayload (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKHistoricalACAD.Payload :=
  let base := LRUpperKReplayCertificate.auto sqrtFuel logFuel box
  { base := base
    qY0LowerPrime := LRQPointCertificate.auto (sqrtFuel + 8) (logFuel + 8)
      (y0AD box).value.lower
    qY0SqrtLower := RationalEnclosure.autoSqrtCertificate (sqrtFuel + 8)
      (RationalEnclosure.point (y0AD box).value.lower)
    sqrtE := RationalEnclosure.autoSqrtCertificate (sqrtFuel + 8)
      (eAD box).value }

/-- All deterministic scalar corner checks used by the four historical
primitive value projections. -/
def cornerChecks (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Bool :=
  aCornerCheck sqrtFuel logFuel box (y0AD box).value &&
    cCornerCheck sqrtFuel logFuel box (y0AD box).value &&
    aCornerCheck sqrtFuel logFuel box (eAD box).value &&
    cCornerCheck sqrtFuel logFuel box (eAD box).value

def payloadCheck (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  let payload := autoPayload sqrtFuel logFuel box
  LRUpperKHistoricalACAD.check terms box payload &&
    cornerChecks sqrtFuel logFuel box

def evaluation (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : MidpointCertificate :=
  let center := centerBox box
  let centerPayload := autoPayload sqrtFuel logFuel center
  let derivativePayload := autoPayload sqrtFuel logFuel box
  let centerNode := evaluateAD terms center centerPayload
  let derivativeNode := evaluateAD terms box derivativePayload
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

def check (terms sqrtFuel logFuel : ℕ) (box : CertificateBox) : Bool :=
  openChartBoxCheck box &&
    payloadCheck terms sqrtFuel logFuel (centerBox box) &&
    payloadCheck terms sqrtFuel logFuel box &&
    (evaluation terms sqrtFuel logFuel box).check box

end LRUpperKHistoricalConcreteEvaluator
end CourtadeKumar
