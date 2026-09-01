import InformationTheory.CourtadeKumar.LRCompactVFixedDyadicIntervalCore

/-!
# Fused fixed-dyadic centered monotone-convex evaluator

This is the proof-free executable layer for the two compact-`V`
monotonicity terminals. It evaluates only `P`, `P_v`, `P_x`, and `P_xx`.
All endpoints have the common implicit denominator `2^bits`; every product
is rounded immediately back to that denominator, so an `N`-term evaluation
costs `O(N)` fixed-width operations and never constructs growing rational
denominators.

The expensive `R`/`lambda` score stream is shared. `evalMonotoneCorner` and
`evalMonotoneTangent` each use one fused `N`-step loop rather than invoking a
generic four-output evaluator three times:

* the corner loop evaluates `P` at `(vHi,xHi)`, `P_v` on the full rectangle,
  and `P_x` at `vHi` on the full `x` interval;
* the tangent loop evaluates `P,P_x` together at `(vHi,xCenter)`, `P_v` on
  the full rectangle, and `P_xx` at `vHi` on the full `x` interval.

Thus each index computes the score and signed coefficient `A_n` once. The
top/full `v` streams and center/full `x` streams are also shared, so each
index advances only two `v` and two `x` power recurrences and evaluates only
the three or four weighted-head contributions consumed by the terminal.

## Exact recurrence invariants

After `k` loop iterations, the next index is `n=k+1`.
`CoefficientState` runs the two endpoint recurrences. Its lower-`R` state
encloses `w_n(RLo)` and its upper-`R` state encloses `w_n(RHi)`. Each also
maintains the already-correlated increment base
`q_n=(1-R)^2 R^(n-1)`, with update

`w_(n+1) = w_n + n * (1-R)^2 * R^(n-1)`.

Monotonicity in `R` then forms the shared score enclosure from the lower
endpoint of `w_n(RHi)` and the upper endpoint of `w_n(RLo)`. This avoids the
dependency widening of multiplying `(1-R)^2` and `R^(n-1)` as independent
box intervals.

For every active `x` stream, `XPowerState` encloses

* `xPowPrevPrev=x^(n-2)` (one for the truncated `n=1` exponent),
  `xPowPrev=x^(n-1)`, and `xPow=x^n`;

For every active `v` stream, `VPowerState` encloses
`vPowEven=v^(2n-2)` and `vPowOdd=v^(2n-1)`.

The `x` powers shift by one multiplication; both `v` powers advance by the
precomputed factor `v^2`. With `m=2n-1`, one term uses

`U_n=(1+v)(1+v^m)`,

`U'_n=1+v^m+(1+v)m v^(m-1)`, and

`A_n=(1+lambda)w_n-lambda`.

The coefficient `a_n=1/(2n(2n-1))` uses divisor `2n(2n-1)` for `P,P_v`,
reduced divisor `2(2n-1)` for `P_x`, and factor `n-1` over `2(2n-1)` for
`P_xx`. Completed heads pay `4vxW_R(1)`, `4xW_R(1)`, and `4vW_R(1)` in
`P,P_v,P_x`; `P_xx` has no endpoint term.

No analytic definition, theorem, or real number is imported here. A
separate soundness module will prove these documented invariants.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVCenteredMonotoneEval

open LRCompactVFixedDyadic

/-- Clamp a nonnegative interval to the fixed-dyadic `[0,1]`. -/
def clampUnit (bits : ℕ) (interval : NatInterval) : NatInterval :=
  let denominator := scale bits
  ⟨min interval.lower denominator, min interval.upper denominator⟩

/-- Outward fixed-dyadic interval for `1-x`, after unit clamping. -/
def oneSubUnit (bits : ℕ) (interval : NatInterval) : NatInterval :=
  let bounded := clampUnit bits interval
  let denominator := scale bits
  ⟨denominator - bounded.upper, denominator - bounded.lower⟩

/-- Data shared by every geometry in one fused leaf evaluation. -/
structure SharedInput where
  /-- Exact fixed-dyadic numerator for the checked `lambda`. -/
  lambda : ℕ
  r : NatInterval
  wOne : NatInterval
  deriving DecidableEq, Repr

/-- Shared loop-invariant factors. -/
structure SharedPrepared where
  lambda : NatInterval
  wOne : NatInterval
  one : NatInterval
  onePlusLambda : NatInterval
  rLower : NatInterval
  rUpper : NatInterval
  rLowerGapSquared : NatInterval
  rUpperGapSquared : NatInterval
  deriving DecidableEq, Repr

/-- Factors shared by every output evaluated at one `v` interval. -/
structure VPrepared where
  v : NatInterval
  onePlusV : NatInterval
  vSquared : NatInterval
  deriving DecidableEq, Repr

/-- One clamped `x` interval. -/
structure XPrepared where
  x : NatInterval
  deriving DecidableEq, Repr

def prepareShared (bits : ℕ) (input : SharedInput) : SharedPrepared :=
  let one := NatInterval.one bits
  let lambda := NatInterval.point input.lambda
  let r := clampUnit bits input.r
  let rLower := NatInterval.point r.lower
  let rUpper := NatInterval.point r.upper
  let rLowerGap := oneSubUnit bits rLower
  let rUpperGap := oneSubUnit bits rUpper
  { lambda := lambda
    wOne := input.wOne
    one := one
    onePlusLambda := one.add lambda
    rLower := rLower
    rUpper := rUpper
    rLowerGapSquared := rLowerGap.mul bits rLowerGap
    rUpperGapSquared := rUpperGap.mul bits rUpperGap }

def prepareV (bits : ℕ) (one vInput : NatInterval) : VPrepared :=
  let v := clampUnit bits vInput
  { v := v
    onePlusV := one.add v
    vSquared := v.mul bits v }

def prepareX (bits : ℕ) (xInput : NatInterval) : XPrepared :=
  { x := clampUnit bits xInput }

/-- One fixed-`R` endpoint recurrence before the next head index. -/
structure ScoreEndpointState where
  score : NatInterval
  incrementBase : NatInterval
  deriving DecidableEq, Repr

def initialScoreEndpointState
    (gapSquared : NatInterval) : ScoreEndpointState :=
  { score := NatInterval.zero
    incrementBase := gapSquared }

/-- Both endpoint score recurrences shared by every geometry. -/
structure CoefficientState where
  atLowerR : ScoreEndpointState
  atUpperR : ScoreEndpointState
  deriving DecidableEq, Repr

def initialCoefficientState (prepared : SharedPrepared) : CoefficientState :=
  { atLowerR := initialScoreEndpointState prepared.rLowerGapSquared
    atUpperR := initialScoreEndpointState prepared.rUpperGapSquared }

/-- Score interval oriented by the analytic antitonicity in `R`. -/
def scoreInterval (bits : ℕ) (state : CoefficientState) : NatInterval :=
  clampUnit bits
    ⟨state.atUpperR.score.lower, state.atLowerR.score.upper⟩

/-- Coefficient data computed once and reused by all active geometries. -/
structure Coefficient where
  a : IntInterval
  constantP : IntInterval
  deriving DecidableEq, Repr

/-- Evaluate `A_n=(1+lambda)w_n-lambda` and `4lambda(1-w_n)`. -/
def coefficient (bits : ℕ) (prepared : SharedPrepared)
    (state : CoefficientState) : Coefficient :=
  let boundedScore := scoreInterval bits state
  let weightedScore := prepared.onePlusLambda.mul bits boundedScore
  let scoreComplement := oneSubUnit bits boundedScore
  { a := weightedScore.toSigned.sub prepared.lambda.toSigned
    constantP :=
      ((prepared.lambda.mul bits scoreComplement).scaleNat 4).toSigned }

/-- Advance one endpoint from `w_n,q_n` to `w_(n+1),q_(n+1)`. -/
def advanceScoreEndpoint (bits n : ℕ) (r : NatInterval)
    (state : ScoreEndpointState) : ScoreEndpointState :=
  let scoreIncrement := state.incrementBase.scaleNat n
  { score := clampUnit bits (state.score.add scoreIncrement)
    incrementBase := state.incrementBase.mul bits r }

/-- Advance both endpoint score recurrences once. -/
def advanceCoefficient (bits : ℕ) (prepared : SharedPrepared) (n : ℕ)
    (state : CoefficientState) : CoefficientState :=
  { atLowerR := advanceScoreEndpoint bits n
      prepared.rLower state.atLowerR
    atUpperR := advanceScoreEndpoint bits n
      prepared.rUpper state.atUpperR }

/-- One `x` power recurrence before the next head index. -/
structure XPowerState where
  xPowPrevPrev : NatInterval
  xPowPrev : NatInterval
  xPow : NatInterval
  deriving DecidableEq, Repr

/-- One `v` power recurrence before the next head index. -/
structure VPowerState where
  vPowEven : NatInterval
  vPowOdd : NatInterval
  deriving DecidableEq, Repr

def initialXPowers (one : NatInterval) (prepared : XPrepared) : XPowerState :=
  { xPowPrevPrev := one
    xPowPrev := one
    xPow := prepared.x }

def initialVPowers (one : NatInterval) (prepared : VPrepared) : VPowerState :=
  { vPowEven := one
    vPowOdd := prepared.v }

def advanceXPowers (bits : ℕ) (prepared : XPrepared)
    (state : XPowerState) : XPowerState :=
  { xPowPrevPrev := state.xPowPrev
    xPowPrev := state.xPow
    xPow := state.xPow.mul bits prepared.x }

def advanceVPowers (bits : ℕ) (prepared : VPrepared)
    (state : VPowerState) : VPowerState :=
  { vPowEven := state.vPowEven.mul bits prepared.vSquared
    vPowOdd := state.vPowOdd.mul bits prepared.vSquared }

/-- The nonnegative factor `U_n=(1+v)(1+v^(2n-1))`. -/
def uShape (bits : ℕ) (one : NatInterval)
    (prepared : VPrepared) (powers : VPowerState) : NatInterval :=
  prepared.onePlusV.mul bits (one.add powers.vPowOdd)

/-- The nonnegative derivative factor
`U'_n=1+v^(2n-1)+(1+v)(2n-1)v^(2n-2)`. -/
def uDerivativeShape (bits : ℕ) (one : NatInterval)
    (prepared : VPrepared) (powers : VPowerState)
    (n : ℕ) : NatInterval :=
  let m := 2 * n - 1
  let onePlusOdd := one.add powers.vPowOdd
  let weightedEven :=
    (prepared.onePlusV.mul bits powers.vPowEven).scaleNat m
  onePlusOdd.add weightedEven

def signedMulTwoNonnegative (bits : ℕ) (signed : IntInterval)
    (first second : NatInterval) : IntInterval :=
  (signed.mulNonnegative bits first).mulNonnegative bits second

def coefficientDenominator (n : ℕ) : ℕ :=
  2 * n * (2 * n - 1)

def xDerivativeDenominator (n : ℕ) : ℕ :=
  2 * (2 * n - 1)

def pContribution (bits n : ℕ) (coefficient : Coefficient)
    (powers : XPowerState) (u : NatInterval) : IntInterval :=
  let varyingPart :=
    signedMulTwoNonnegative bits coefficient.a powers.xPow u
  (varyingPart.add coefficient.constantP).divNat (coefficientDenominator n)

def pvContribution (bits n : ℕ) (coefficient : Coefficient)
    (powers : XPowerState) (uDeriv : NatInterval) : IntInterval :=
  (signedMulTwoNonnegative bits coefficient.a powers.xPow uDeriv).divNat
    (coefficientDenominator n)

def pxContribution (bits n : ℕ) (coefficient : Coefficient)
    (powers : XPowerState) (u : NatInterval) : IntInterval :=
  (signedMulTwoNonnegative bits coefficient.a powers.xPowPrev u).divNat
    (xDerivativeDenominator n)

def pxxContribution (bits n : ℕ) (coefficient : Coefficient)
    (powers : XPowerState) (u : NatInterval) : IntInterval :=
  ((signedMulTwoNonnegative bits coefficient.a
      powers.xPowPrevPrev u).scaleNat (n - 1)).divNat
    (xDerivativeDenominator n)

def pvEndpoint (bits : ℕ) (shared : SharedPrepared)
    (prepared : XPrepared) : IntInterval :=
  ((prepared.x.mul bits shared.wOne).scaleNat 4).toSigned

/-! ## Monotone-corner batch -/

structure MonotoneCornerInput where
  shared : SharedInput
  vFull : NatInterval
  xFull : NatInterval
  vHi : NatInterval
  xHi : NatInterval
  deriving DecidableEq, Repr

structure MonotoneCornerPrepared where
  shared : SharedPrepared
  topV : VPrepared
  fullV : VPrepared
  topX : XPrepared
  fullX : XPrepared
  deriving DecidableEq, Repr

def prepareMonotoneCorner (bits : ℕ)
    (input : MonotoneCornerInput) : MonotoneCornerPrepared :=
  let shared := prepareShared bits input.shared
  { shared := shared
    topV := prepareV bits shared.one input.vHi
    fullV := prepareV bits shared.one input.vFull
    topX := prepareX bits input.xHi
    fullX := prepareX bits input.xFull }

structure MonotoneCornerState where
  coefficient : CoefficientState
  topVPowers : VPowerState
  fullVPowers : VPowerState
  topXPowers : XPowerState
  fullXPowers : XPowerState
  pHead : IntInterval
  pvHead : IntInterval
  pxHead : IntInterval
  deriving DecidableEq, Repr

def initialMonotoneCornerState
    (prepared : MonotoneCornerPrepared) : MonotoneCornerState :=
  { coefficient := initialCoefficientState prepared.shared
    topVPowers := initialVPowers prepared.shared.one prepared.topV
    fullVPowers := initialVPowers prepared.shared.one prepared.fullV
    topXPowers := initialXPowers prepared.shared.one prepared.topX
    fullXPowers := initialXPowers prepared.shared.one prepared.fullX
    pHead := IntInterval.zero
    pvHead := IntInterval.zero
    pxHead := IntInterval.zero }

def monotoneCornerStep (bits : ℕ) (prepared : MonotoneCornerPrepared)
    (n : ℕ) (state : MonotoneCornerState) : MonotoneCornerState :=
  let c := coefficient bits prepared.shared state.coefficient
  let topU := uShape bits prepared.shared.one
    prepared.topV state.topVPowers
  let fullUDeriv := uDerivativeShape bits prepared.shared.one
    prepared.fullV state.fullVPowers n
  { coefficient := advanceCoefficient bits prepared.shared n state.coefficient
    topVPowers := advanceVPowers bits prepared.topV state.topVPowers
    fullVPowers := advanceVPowers bits prepared.fullV state.fullVPowers
    topXPowers := advanceXPowers bits prepared.topX state.topXPowers
    fullXPowers := advanceXPowers bits prepared.fullX state.fullXPowers
    pHead := state.pHead.add
      (pContribution bits n c state.topXPowers topU)
    pvHead := state.pvHead.add
      (pvContribution bits n c state.fullXPowers fullUDeriv)
    pxHead := state.pxHead.add
      (pxContribution bits n c state.fullXPowers topU) }

def runMonotoneCorner (bits : ℕ)
    (prepared : MonotoneCornerPrepared) : ℕ → MonotoneCornerState
  | 0 => initialMonotoneCornerState prepared
  | terms + 1 => monotoneCornerStep bits prepared (terms + 1)
      (runMonotoneCorner bits prepared terms)

structure MonotoneCornerOutput where
  p : IntInterval
  pv : IntInterval
  px : IntInterval
  deriving DecidableEq, Repr

def finishMonotoneCorner (bits : ℕ) (prepared : MonotoneCornerPrepared)
    (state : MonotoneCornerState) : MonotoneCornerOutput :=
  let vHiW := prepared.topV.v.mul bits prepared.shared.wOne
  let pEnd :=
    ((vHiW.mul bits prepared.topX.x).scaleNat 4).toSigned
  let pxEnd := (vHiW.scaleNat 4).toSigned
  { p := state.pHead.sub pEnd
    pv := state.pvHead.sub
      (pvEndpoint bits prepared.shared prepared.fullX)
    px := state.pxHead.sub pxEnd }

def evalMonotoneCorner (bits terms : ℕ)
    (input : MonotoneCornerInput) : MonotoneCornerOutput :=
  let prepared := prepareMonotoneCorner bits input
  finishMonotoneCorner bits prepared
    (runMonotoneCorner bits prepared terms)

structure MonotoneCornerObservation where
  valueLower : ℤ
  vDerivativeUpper : ℤ
  xDerivativeUpper : ℤ
  deriving DecidableEq, Repr

def MonotoneCornerOutput.observe
    (output : MonotoneCornerOutput) : MonotoneCornerObservation :=
  { valueLower := output.p.lower
    vDerivativeUpper := output.pv.upper
    xDerivativeUpper := output.px.upper }

def MonotoneCornerObservation.decreasing
    (observation : MonotoneCornerObservation) : Bool :=
  decide (observation.vDerivativeUpper ≤ 0 ∧
    observation.xDerivativeUpper ≤ 0)

def observeMonotoneCorner (bits terms : ℕ)
    (input : MonotoneCornerInput) : MonotoneCornerObservation :=
  (evalMonotoneCorner bits terms input).observe

/-! ## Monotone-convex tangent batch -/

structure MonotoneTangentInput where
  shared : SharedInput
  vFull : NatInterval
  xFull : NatInterval
  vHi : NatInterval
  xCenter : NatInterval
  deriving DecidableEq, Repr

structure MonotoneTangentPrepared where
  shared : SharedPrepared
  topV : VPrepared
  fullV : VPrepared
  centerX : XPrepared
  fullX : XPrepared
  deriving DecidableEq, Repr

def prepareMonotoneTangent (bits : ℕ)
    (input : MonotoneTangentInput) : MonotoneTangentPrepared :=
  let shared := prepareShared bits input.shared
  { shared := shared
    topV := prepareV bits shared.one input.vHi
    fullV := prepareV bits shared.one input.vFull
    centerX := prepareX bits input.xCenter
    fullX := prepareX bits input.xFull }

structure MonotoneTangentState where
  coefficient : CoefficientState
  topVPowers : VPowerState
  fullVPowers : VPowerState
  centerXPowers : XPowerState
  fullXPowers : XPowerState
  pHead : IntInterval
  pvHead : IntInterval
  pxHead : IntInterval
  pxxHead : IntInterval
  deriving DecidableEq, Repr

def initialMonotoneTangentState
    (prepared : MonotoneTangentPrepared) : MonotoneTangentState :=
  { coefficient := initialCoefficientState prepared.shared
    topVPowers := initialVPowers prepared.shared.one prepared.topV
    fullVPowers := initialVPowers prepared.shared.one prepared.fullV
    centerXPowers := initialXPowers prepared.shared.one prepared.centerX
    fullXPowers := initialXPowers prepared.shared.one prepared.fullX
    pHead := IntInterval.zero
    pvHead := IntInterval.zero
    pxHead := IntInterval.zero
    pxxHead := IntInterval.zero }

def monotoneTangentStep (bits : ℕ) (prepared : MonotoneTangentPrepared)
    (n : ℕ) (state : MonotoneTangentState) : MonotoneTangentState :=
  let c := coefficient bits prepared.shared state.coefficient
  let topU := uShape bits prepared.shared.one
    prepared.topV state.topVPowers
  let fullUDeriv := uDerivativeShape bits prepared.shared.one
    prepared.fullV state.fullVPowers n
  { coefficient := advanceCoefficient bits prepared.shared n state.coefficient
    topVPowers := advanceVPowers bits prepared.topV state.topVPowers
    fullVPowers := advanceVPowers bits prepared.fullV state.fullVPowers
    centerXPowers := advanceXPowers bits prepared.centerX state.centerXPowers
    fullXPowers := advanceXPowers bits prepared.fullX state.fullXPowers
    pHead := state.pHead.add
      (pContribution bits n c state.centerXPowers topU)
    pvHead := state.pvHead.add
      (pvContribution bits n c state.fullXPowers fullUDeriv)
    pxHead := state.pxHead.add
      (pxContribution bits n c state.centerXPowers topU)
    pxxHead := state.pxxHead.add
      (pxxContribution bits n c state.fullXPowers topU) }

def runMonotoneTangent (bits : ℕ)
    (prepared : MonotoneTangentPrepared) : ℕ → MonotoneTangentState
  | 0 => initialMonotoneTangentState prepared
  | terms + 1 => monotoneTangentStep bits prepared (terms + 1)
      (runMonotoneTangent bits prepared terms)

structure MonotoneTangentOutput where
  p : IntInterval
  pv : IntInterval
  px : IntInterval
  pxx : IntInterval
  deriving DecidableEq, Repr

def finishMonotoneTangent (bits : ℕ) (prepared : MonotoneTangentPrepared)
    (state : MonotoneTangentState) : MonotoneTangentOutput :=
  let vHiW := prepared.topV.v.mul bits prepared.shared.wOne
  let pEnd :=
    ((vHiW.mul bits prepared.centerX.x).scaleNat 4).toSigned
  let pxEnd := (vHiW.scaleNat 4).toSigned
  { p := state.pHead.sub pEnd
    pv := state.pvHead.sub
      (pvEndpoint bits prepared.shared prepared.fullX)
    px := state.pxHead.sub pxEnd
    pxx := state.pxxHead }

def evalMonotoneTangent (bits terms : ℕ)
    (input : MonotoneTangentInput) : MonotoneTangentOutput :=
  let prepared := prepareMonotoneTangent bits input
  finishMonotoneTangent bits prepared
    (runMonotoneTangent bits prepared terms)

structure MonotoneTangentObservation where
  valueLower : ℤ
  xGradientMaxAbs : ℕ
  vDerivativeUpper : ℤ
  xSecondDerivativeLower : ℤ
  deriving DecidableEq, Repr

def MonotoneTangentOutput.observe
    (output : MonotoneTangentOutput) : MonotoneTangentObservation :=
  { valueLower := output.p.lower
    xGradientMaxAbs := output.px.maxAbs
    vDerivativeUpper := output.pv.upper
    xSecondDerivativeLower := output.pxx.lower }

def MonotoneTangentObservation.vDecreasing
    (observation : MonotoneTangentObservation) : Bool :=
  decide (observation.vDerivativeUpper ≤ 0)

def MonotoneTangentObservation.xConvex
    (observation : MonotoneTangentObservation) : Bool :=
  decide (0 ≤ observation.xSecondDerivativeLower)

def observeMonotoneTangent (bits terms : ℕ)
    (input : MonotoneTangentInput) : MonotoneTangentObservation :=
  (evalMonotoneTangent bits terms input).observe

end LRCompactVCenteredMonotoneEval
end CourtadeKumar
