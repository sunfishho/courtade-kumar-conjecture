import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneConfigCore
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneEvalCore
import InformationTheory.CourtadeKumar.LRCompactVSameYLambda

/-!
# Executable centered-monotone compact-`V` leaf rows

This executable-only layer packages one adjacent `v` strip, reconstructs its
exact rational `CertificateBox`, and runs one of the two fused fixed-dyadic
evaluators.  The precision, channel interval, squared-shape interval, and
endpoint-kernel enclosure are shared configuration rather than row payload.

Each row stores only its `v` endpoints, checked dyadic multiplier, finite-head
choice, terminal geometry, and the range reduction for `log (1 + vHi)`.  The
checker combines the exact same-`y` budget and slope conditions with the
integer sign or tangent-radius conditions consumed by the later soundness
adapter.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVCenteredMonotoneLeaf

open LRCompactVFixedDyadic
open LRCompactVCenteredMonotoneEval

/-- The only finite-head lengths used by the adjacent terminal family. -/
inductive HeadChoice where
  | n128
  | n192
  deriving DecidableEq, Repr

namespace HeadChoice

/-- Decode the compact head tag to the evaluator's term count. -/
def terms : HeadChoice → ℕ
  | .n128 => 128
  | .n192 => 192

end HeadChoice

/-- Geometry used to transport an endpoint value across the common `x`
interval.  Tangent centers are exact fixed-dyadic numerators. -/
inductive Geometry where
  | corner
  | tangent (centerNum : ℕ)
  deriving DecidableEq, Repr

/-- Minimal per-strip payload for a centered monotone terminal. -/
structure Row where
  vLoNum : ℕ
  vHiNum : ℕ
  lambdaNum : ℕ
  head : HeadChoice
  geometry : Geometry
  logOnePlusVHi : RationalEnclosure.LogRangeCertificate

namespace Row

/-- Exact rational box reconstructed from the row and common configuration. -/
def box (row : Row) : CertificateBox where
  sLo := LRCompactVCenteredMonotoneConfig.rootBox.sLo
  sHi := LRCompactVCenteredMonotoneConfig.rootBox.sHi
  kLo := decodeNat LRCompactVCenteredMonotoneConfig.bits row.vLoNum
  kHi := decodeNat LRCompactVCenteredMonotoneConfig.bits row.vHiNum
  chiLo := LRCompactVCenteredMonotoneConfig.rootBox.chiLo
  chiHi := LRCompactVCenteredMonotoneConfig.rootBox.chiHi

/-- Exact rational value of the row's checked dyadic multiplier. -/
def lambda (row : Row) : ℚ :=
  decodeNat LRCompactVCenteredMonotoneConfig.bits row.lambdaNum

/-- Fixed-dyadic interval for the full `v` strip. -/
def vInterval (row : Row) : NatInterval :=
  ⟨row.vLoNum, row.vHiNum⟩

/-- Common evaluator input specialized to this row's multiplier. -/
def sharedInput (row : Row) : SharedInput where
  lambda := row.lambdaNum
  r := LRCompactVCenteredMonotoneConfig.rInterval
  wOne := LRCompactVCenteredMonotoneConfig.wOne

/-- Fused monotone-corner input.  Both analytic endpoints are constructed as
exact singleton intervals rather than being stored in the row. -/
def cornerInput (row : Row) : MonotoneCornerInput where
  shared := row.sharedInput
  vFull := row.vInterval
  xFull := LRCompactVCenteredMonotoneConfig.xInterval
  vHi := NatInterval.point row.vHiNum
  xHi := NatInterval.point
    LRCompactVCenteredMonotoneConfig.xInterval.upper

/-- Fused monotone-convex input at an exact dyadic center. -/
def tangentInput (row : Row) (centerNum : ℕ) : MonotoneTangentInput where
  shared := row.sharedInput
  vFull := row.vInterval
  xFull := LRCompactVCenteredMonotoneConfig.xInterval
  vHi := NatInterval.point row.vHiNum
  xCenter := NatInterval.point centerNum

/-- Maximum fixed-dyadic distance from the tangent center to either common
`x` endpoint. -/
def tangentRadiusNum (centerNum : ℕ) : ℕ :=
  max (centerNum - LRCompactVCenteredMonotoneConfig.xInterval.lower)
    (LRCompactVCenteredMonotoneConfig.xInterval.upper - centerNum)

/-- Same-`y` enclosure of `B` at the row's upper `v` endpoint. -/
def bEndpoint (logTerms halfLogTerms : ℕ) (row : Row) :
    RationalEnclosure :=
  lrCompactVSameYBEndpointEnclosure logTerms halfLogTerms row.box
    row.logOnePlusVHi

/-- Direct positive-series enclosure of `D` for the row. -/
def dEnclosure (dTerms : ℕ) (row : Row) : RationalEnclosure :=
  lrCompactVDirectDEnclosure dTerms row.box

/-- Cheap structural checks that keep every row inside the common adjacent
`v` range. -/
def rangeCheck (row : Row) : Bool :=
  decide (LRCompactVCenteredMonotoneConfig.vRootInterval.lower ≤
      row.vLoNum ∧
    row.vLoNum ≤ row.vHiNum ∧
    row.vHiNum ≤ LRCompactVCenteredMonotoneConfig.vRootInterval.upper)

/-- Exact checked-lambda obligations used by the same-`y` soundness theorem. -/
def sameYCheck (logTerms halfLogTerms dTerms : ℕ) (row : Row) : Bool :=
  let box := row.box
  let bEndpoint := row.bEndpoint logTerms halfLogTerms
  let d := row.dEnclosure dTerms
  decide (
    row.logOnePlusVHi.check (1 + box.kHi) = true ∧
    LRCompactVDirectDValid.check box = true ∧
    row.lambda * bEndpoint.upper ≤ d.nonnegativeLower ∧
    row.lambda * box.sHi * (1 - lrCompactVDirectDYLoQ box) ≤
      1 - box.sHi)

/-- Observe the corner batch exactly once. -/
def cornerObservation (row : Row) : MonotoneCornerObservation :=
  observeMonotoneCorner LRCompactVCenteredMonotoneConfig.bits
    row.head.terms row.cornerInput

/-- Integer terminal conditions for the monotone-corner theorem. -/
def cornerCheck (row : Row) : Bool :=
  let observation := row.cornerObservation
  decide (0 ≤ observation.valueLower ∧
    observation.vDerivativeUpper ≤ 0 ∧
    observation.xDerivativeUpper ≤ 0)

/-- Observe the tangent batch exactly once. -/
def tangentObservation (row : Row) (centerNum : ℕ) :
    MonotoneTangentObservation :=
  observeMonotoneTangent LRCompactVCenteredMonotoneConfig.bits row.head.terms
    (row.tangentInput centerNum)

/-- Integer terminal conditions for the monotone-convex theorem.  The
upward-rounded gradient-radius product is compared directly with the signed
value lower numerator at the common scale. -/
def tangentCheck (row : Row) (centerNum : ℕ) : Bool :=
  let observation := row.tangentObservation centerNum
  let radiusNum := tangentRadiusNum centerNum
  decide (LRCompactVCenteredMonotoneConfig.xInterval.lower ≤ centerNum ∧
    centerNum ≤ LRCompactVCenteredMonotoneConfig.xInterval.upper ∧
    observation.vDerivativeUpper ≤ 0 ∧
    0 ≤ observation.xSecondDerivativeLower ∧
    Int.ofNat (mulUp LRCompactVCenteredMonotoneConfig.bits
      observation.xGradientMaxAbs radiusNum) ≤
      observation.valueLower)

/-- Complete executable check for one adjacent centered-monotone row. -/
def check (logTerms halfLogTerms dTerms : ℕ) (row : Row) : Bool :=
  row.rangeCheck && row.sameYCheck logTerms halfLogTerms dTerms &&
    match row.geometry with
    | .corner => row.cornerCheck
    | .tangent centerNum => row.tangentCheck centerNum

/-- Exact binding between an external subdivision leaf and the box derived
from the compact row payload. -/
def boxMatches (box : CertificateBox) (row : Row) : Bool :=
  decide (box.sLo = row.box.sLo ∧ box.sHi = row.box.sHi ∧
    box.kLo = row.box.kLo ∧ box.kHi = row.box.kHi ∧
    box.chiLo = row.box.chiLo ∧ box.chiHi = row.box.chiHi)

/-- Check a row only after authenticating the external subdivision box. -/
def checkAt (logTerms halfLogTerms dTerms : ℕ)
    (box : CertificateBox) (row : Row) : Bool :=
  boxMatches box row && row.check logTerms halfLogTerms dTerms

end Row
end LRCompactVCenteredMonotoneLeaf
end CourtadeKumar
