import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneEvalCore
import InformationTheory.CourtadeKumar.LRCompactVFixedDyadicIntervalSound
import InformationTheory.CourtadeKumar.LRCompactVLambdaCenteredPolynomialDerivatives

/-!
# Soundness of the fused centered monotone-convex evaluator

This module is the semantic half of
`LRCompactVCenteredMonotoneEvalCore`.  It proves the fixed-dyadic score,
power, shape, and finite-head recurrences compositionally, then exposes the
four endpoint inequalities consumed by the monotone-corner and
monotone-convex terminal theorems.

The executable core intentionally imports no real analysis.  Conversely,
this file contains no generated terminal data and no leaf budget or radius
arithmetic.  A later leaf adapter can therefore combine these interval
guarantees with the analytic terminal without enlarging the evaluator's
trusted computation surface.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace CourtadeKumar
namespace LRCompactVFixedDyadic
namespace NatInterval

/-- A fixed-dyadic interval covers every rational in the displayed range.
This is the seed bridge used when a certificate endpoint, such as `9/10`,
is not itself dyadic. -/
def CoversRatRange (interval : NatInterval) (bits : ℕ) (lo hi : ℚ) : Prop :=
  decodeNat bits interval.lower ≤ lo ∧
    hi ≤ decodeNat bits interval.upper

/-- Rational range coverage implies real containment of every point in the
range. -/
theorem contains_of_coversRatRange
    {interval : NatInterval} {bits : ℕ} {lo hi : ℚ} {x : ℝ}
    (hcover : interval.CoversRatRange bits lo hi)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    interval.Contains bits x := by
  rcases hcover with ⟨hcoverLo, hcoverHi⟩
  constructor
  · have hcoverLoR :
        (decodeNat bits interval.lower : ℝ) ≤ (lo : ℝ) := by
      exact_mod_cast hcoverLo
    exact hcoverLoR.trans hlo
  · have hcoverHiR :
        (hi : ℝ) ≤ (decodeNat bits interval.upper : ℝ) := by
      exact_mod_cast hcoverHi
    exact hhi.trans hcoverHiR

end NatInterval
end LRCompactVFixedDyadic

namespace LRCompactVCenteredMonotoneEval

open LRCompactVFixedDyadic

@[simp]
theorem decodeNat_scale_real (bits : ℕ) :
    (decodeNat bits (scale bits) : ℝ) = 1 := by
  norm_num [decodeNat, scale]

theorem decodeNat_scale_sub_real
    {bits value : ℕ} (hvalue : value ≤ scale bits) :
    (decodeNat bits (scale bits - value) : ℝ) =
      1 - (decodeNat bits value : ℝ) := by
  have hadd := decodeNat_add_real bits (scale bits - value) value
  rw [Nat.sub_add_cancel hvalue, decodeNat_scale_real] at hadd
  linarith

/-- Unit clamping preserves every represented point already known to lie in
the unit interval. -/
theorem clampUnit_contains
    {bits : ℕ} {interval : NatInterval} {x : ℝ}
    (hx : interval.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (clampUnit bits interval).Contains bits x := by
  rcases hx with ⟨hxLower, hxUpper⟩
  constructor
  · change
      (decodeNat bits (min interval.lower (scale bits)) : ℝ) ≤ x
    by_cases hle : interval.lower ≤ scale bits
    · rw [min_eq_left hle]
      exact hxLower
    · have hscale : scale bits ≤ interval.lower := by omega
      rw [min_eq_right hscale]
      exact (IntInterval.decodeNat_mono hscale).trans hxLower
  · change x ≤
      (decodeNat bits (min interval.upper (scale bits)) : ℝ)
    by_cases hle : interval.upper ≤ scale bits
    · rw [min_eq_left hle]
      exact hxUpper
    · have hscale : scale bits ≤ interval.upper := by omega
      rw [min_eq_right hscale, decodeNat_scale_real]
      exact hx1

/-- Fixed-dyadic unit complementation is outward sound. -/
theorem oneSubUnit_contains
    {bits : ℕ} {interval : NatInterval} {x : ℝ}
    (hx : interval.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (oneSubUnit bits interval).Contains bits (1 - x) := by
  let bounded := clampUnit bits interval
  have hbounded : bounded.Contains bits x :=
    clampUnit_contains hx hx0 hx1
  have hlower : bounded.lower ≤ scale bits := by
    simp [bounded, clampUnit]
  have hupper : bounded.upper ≤ scale bits := by
    simp [bounded, clampUnit]
  change
    (decodeNat bits (scale bits - bounded.upper) : ℝ) ≤ 1 - x ∧
      1 - x ≤
        (decodeNat bits (scale bits - bounded.lower) : ℝ)
  rw [decodeNat_scale_sub_real hupper,
    decodeNat_scale_sub_real hlower]
  exact ⟨sub_le_sub_left hbounded.2 1,
    sub_le_sub_left hbounded.1 1⟩

/-- Real value represented by the exact fixed-dyadic lambda numerator. -/
def lambdaValue (bits : ℕ) (input : SharedInput) : ℝ :=
  (decodeNat bits input.lambda : ℝ)

/-- Exact real endpoints of the clamped fixed-dyadic `R` interval. -/
def rLowerValue (bits : ℕ) (input : SharedInput) : ℝ :=
  (decodeNat bits (clampUnit bits input.r).lower : ℝ)

def rUpperValue (bits : ℕ) (input : SharedInput) : ℝ :=
  (decodeNat bits (clampUnit bits input.r).upper : ℝ)

theorem prepareShared_lambda_contains (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).lambda.Contains bits
      (lambdaValue bits input) := by
  exact NatInterval.point_contains bits input.lambda

theorem prepareShared_onePlusLambda_contains
    (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).onePlusLambda.Contains bits
      (1 + lambdaValue bits input) := by
  exact NatInterval.add_contains (NatInterval.one_contains bits)
    (prepareShared_lambda_contains bits input)

theorem prepareShared_rLower_contains (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).rLower.Contains bits
      (rLowerValue bits input) := by
  exact NatInterval.point_contains bits (clampUnit bits input.r).lower

theorem prepareShared_rUpper_contains (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).rUpper.Contains bits
      (rUpperValue bits input) := by
  exact NatInterval.point_contains bits (clampUnit bits input.r).upper

theorem rLowerValue_mem_unit (bits : ℕ) (input : SharedInput) :
    rLowerValue bits input ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact decodeNat_real_nonnegative bits _
  · unfold rLowerValue
    have hle : (clampUnit bits input.r).lower ≤ scale bits := by
      simp [clampUnit]
    simpa only [decodeNat_scale_real] using
      IntInterval.decodeNat_mono (bits := bits) hle

theorem rUpperValue_mem_unit (bits : ℕ) (input : SharedInput) :
    rUpperValue bits input ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact decodeNat_real_nonnegative bits _
  · unfold rUpperValue
    have hle : (clampUnit bits input.r).upper ≤ scale bits := by
      simp [clampUnit]
    simpa only [decodeNat_scale_real] using
      IntInterval.decodeNat_mono (bits := bits) hle

theorem rLowerValue_le_rUpperValue
    {bits : ℕ} {input : SharedInput} {R : ℝ}
    (hR : input.r.Contains bits R) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    rLowerValue bits input ≤ rUpperValue bits input := by
  have hclamp := clampUnit_contains hR hR0 hR1
  exact hclamp.1.trans hclamp.2

/-- Exact positive score increment identity in the index convention used by
the executable loop. -/
theorem lrCompactVScore_succ_eq
    (R : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lrCompactVScore R (n + 1) =
      lrCompactVScore R n +
        (n : ℝ) * (1 - R) ^ 2 * R ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hstep := lrCompactVScore_succ_succ_sub R k
  have hindex : 1 + k = k + 1 := by omega
  rw [hindex, show k + 1 + 1 = k + 2 by omega,
    show k + 1 - 1 = k by omega]
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Semantic invariant of one endpoint score recurrence before index `n`. -/
structure ScoreEndpointSound
    (bits n : ℕ) (R : ℝ) (state : ScoreEndpointState) : Prop where
  score : state.score.Contains bits (lrCompactVScore R n)
  incrementBase : state.incrementBase.Contains bits
    ((1 - R) ^ 2 * R ^ (n - 1))

theorem initialScoreEndpointState_sound
    {bits : ℕ} {R : ℝ} {gapSquared : NatInterval}
    (hgap : gapSquared.Contains bits ((1 - R) ^ 2)) :
    ScoreEndpointSound bits 1 R
      (initialScoreEndpointState gapSquared) := by
  constructor
  · simpa [initialScoreEndpointState, lrCompactVScore_one] using
      NatInterval.zero_contains bits
  · simpa [initialScoreEndpointState] using hgap

theorem advanceScoreEndpoint_sound
    {bits n : ℕ} {R : ℝ} {r : NatInterval}
    {state : ScoreEndpointState}
    (hn : 1 ≤ n) (hRmem : R ∈ Icc (0 : ℝ) 1)
    (hr : r.Contains bits R)
    (hstate : ScoreEndpointSound bits n R state) :
    ScoreEndpointSound bits (n + 1) R
      (advanceScoreEndpoint bits n r state) := by
  constructor
  · have hincrement := NatInterval.scaleNat_contains
      (coefficient := n) hstate.incrementBase
    have hadd := NatInterval.add_contains hstate.score hincrement
    have hraw : (state.score.add (state.incrementBase.scaleNat n)).Contains bits
        (lrCompactVScore R (n + 1)) := by
      rw [lrCompactVScore_succ_eq R hn]
      convert hadd using 1 <;> ring
    exact clampUnit_contains hraw
      (lrCompactVScore_nonneg hRmem.1 (by omega))
      (lrCompactVScore_le_one hRmem (by omega))
  · have hmul := NatInterval.mul_contains hstate.incrementBase hr
    change (state.incrementBase.mul bits r).Contains bits
      ((1 - R) ^ 2 * R ^ n)
    have hpow : R ^ n = R ^ (n - 1) * R := by
      conv_lhs =>
        rw [show n = (n - 1) + 1 by omega, pow_succ]
    rw [hpow]
    simpa only [mul_assoc] using hmul

/-- Paired endpoint invariant for the shared coefficient stream. -/
structure CoefficientStateSound
    (bits n : ℕ) (rLo rHi : ℝ) (state : CoefficientState) : Prop where
  atLowerR : ScoreEndpointSound bits n rLo state.atLowerR
  atUpperR : ScoreEndpointSound bits n rHi state.atUpperR

theorem scoreInterval_contains
    {bits n : ℕ} {rLo rHi R : ℝ} {state : CoefficientState}
    (hn : 1 ≤ n) (hrLo : rLo ∈ Icc (0 : ℝ) 1)
    (hrHi : rHi ∈ Icc (0 : ℝ) 1)
    (hR : R ∈ Icc (0 : ℝ) 1)
    (hlo : rLo ≤ R) (hhi : R ≤ rHi)
    (hstate : CoefficientStateSound bits n rLo rHi state) :
    (scoreInterval bits state).Contains bits (lrCompactVScore R n) := by
  have hanti := lrCompactVScore_antitoneOn_unit hn
  have hlower :
      (decodeNat bits state.atUpperR.score.lower : ℝ) ≤
        lrCompactVScore R n :=
    hstate.atUpperR.score.1.trans (hanti hR hrHi hhi)
  have hupper :
      lrCompactVScore R n ≤
        (decodeNat bits state.atLowerR.score.upper : ℝ) :=
    (hanti hrLo hR hlo).trans hstate.atLowerR.score.2
  exact clampUnit_contains ⟨hlower, hupper⟩
    (lrCompactVScore_nonneg hR.1 hn)
    (lrCompactVScore_le_one hR hn)

/-! ## Prepared geometry and power recurrences -/

/-- Semantic invariant for a clamped `v` input and its two cached factors. -/
structure VPreparedSound
    (bits : ℕ) (v : ℝ) (prepared : VPrepared) : Prop where
  value : prepared.v.Contains bits v
  onePlusV : prepared.onePlusV.Contains bits (1 + v)
  vSquared : prepared.vSquared.Contains bits (v ^ 2)

/-- Semantic invariant for a clamped `x` input. -/
structure XPreparedSound
    (bits : ℕ) (x : ℝ) (prepared : XPrepared) : Prop where
  value : prepared.x.Contains bits x

theorem prepareV_sound
    {bits : ℕ} {one vInput : NatInterval} {v : ℝ}
    (hone : one.Contains bits 1)
    (hv : vInput.Contains bits v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    VPreparedSound bits v (prepareV bits one vInput) := by
  have hvBounded := clampUnit_contains hv hv0 hv1
  constructor
  · simpa [prepareV] using hvBounded
  · simpa [prepareV] using NatInterval.add_contains hone hvBounded
  · simpa [prepareV, pow_two] using
      NatInterval.mul_contains hvBounded hvBounded

theorem prepareX_sound
    {bits : ℕ} {xInput : NatInterval} {x : ℝ}
    (hx : xInput.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    XPreparedSound bits x (prepareX bits xInput) := by
  constructor
  simpa [prepareX] using clampUnit_contains hx hx0 hx1

theorem prepareShared_rLowerGapSquared_contains
    (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).rLowerGapSquared.Contains bits
      ((1 - rLowerValue bits input) ^ 2) := by
  have hR := prepareShared_rLower_contains bits input
  have hunit := rLowerValue_mem_unit bits input
  have hgap := oneSubUnit_contains hR hunit.1 hunit.2
  have hsquare := NatInterval.mul_contains hgap hgap
  simpa [prepareShared, pow_two] using hsquare

theorem prepareShared_rUpperGapSquared_contains
    (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).rUpperGapSquared.Contains bits
      ((1 - rUpperValue bits input) ^ 2) := by
  have hR := prepareShared_rUpper_contains bits input
  have hunit := rUpperValue_mem_unit bits input
  have hgap := oneSubUnit_contains hR hunit.1 hunit.2
  have hsquare := NatInterval.mul_contains hgap hgap
  simpa [prepareShared, pow_two] using hsquare

theorem initialCoefficientState_sound (bits : ℕ) (input : SharedInput) :
    CoefficientStateSound bits 1
      (rLowerValue bits input) (rUpperValue bits input)
      (initialCoefficientState (prepareShared bits input)) := by
  constructor
  · simpa [initialCoefficientState] using
      initialScoreEndpointState_sound
        (prepareShared_rLowerGapSquared_contains bits input)
  · simpa [initialCoefficientState] using
      initialScoreEndpointState_sound
        (prepareShared_rUpperGapSquared_contains bits input)

theorem advanceCoefficient_sound
    {bits n : ℕ} {input : SharedInput} {state : CoefficientState}
    (hn : 1 ≤ n)
    (hstate : CoefficientStateSound bits n
      (rLowerValue bits input) (rUpperValue bits input) state) :
    CoefficientStateSound bits (n + 1)
      (rLowerValue bits input) (rUpperValue bits input)
      (advanceCoefficient bits (prepareShared bits input) n state) := by
  constructor
  · simpa [advanceCoefficient] using
      advanceScoreEndpoint_sound hn
        (rLowerValue_mem_unit bits input)
        (prepareShared_rLower_contains bits input) hstate.atLowerR
  · simpa [advanceCoefficient] using
      advanceScoreEndpoint_sound hn
        (rUpperValue_mem_unit bits input)
        (prepareShared_rUpper_contains bits input) hstate.atUpperR

/-- Semantic invariant for the three consecutive `x` powers used before
head index `n`. Natural subtraction gives the intended truncated exponent at
`n=1`. -/
structure XPowerStateSound
    (bits n : ℕ) (x : ℝ) (state : XPowerState) : Prop where
  xPowPrevPrev : state.xPowPrevPrev.Contains bits (x ^ (n - 2))
  xPowPrev : state.xPowPrev.Contains bits (x ^ (n - 1))
  xPow : state.xPow.Contains bits (x ^ n)

/-- Semantic invariant for the even/odd `v` powers used before head index
`n`. -/
structure VPowerStateSound
    (bits n : ℕ) (v : ℝ) (state : VPowerState) : Prop where
  vPowEven : state.vPowEven.Contains bits (v ^ (2 * n - 2))
  vPowOdd : state.vPowOdd.Contains bits (v ^ (2 * n - 1))

theorem initialXPowers_sound
    {bits : ℕ} {one : NatInterval} {prepared : XPrepared} {x : ℝ}
    (hone : one.Contains bits 1)
    (hprepared : XPreparedSound bits x prepared) :
    XPowerStateSound bits 1 x (initialXPowers one prepared) := by
  constructor
  · simpa [initialXPowers] using hone
  · simpa [initialXPowers] using hone
  · simpa [initialXPowers] using hprepared.value

theorem advanceXPowers_sound
    {bits n : ℕ} {prepared : XPrepared} {state : XPowerState}
    {x : ℝ} (hn : 1 ≤ n)
    (hprepared : XPreparedSound bits x prepared)
    (hstate : XPowerStateSound bits n x state) :
    XPowerStateSound bits (n + 1) x
      (advanceXPowers bits prepared state) := by
  constructor
  · simpa [advanceXPowers, show n + 1 - 2 = n - 1 by omega] using
      hstate.xPowPrev
  · simpa [advanceXPowers, show n + 1 - 1 = n by omega] using
      hstate.xPow
  · have hmul := NatInterval.mul_contains hstate.xPow hprepared.value
    simpa [advanceXPowers, pow_succ] using hmul

theorem initialVPowers_sound
    {bits : ℕ} {one : NatInterval} {prepared : VPrepared} {v : ℝ}
    (hone : one.Contains bits 1)
    (hprepared : VPreparedSound bits v prepared) :
    VPowerStateSound bits 1 v (initialVPowers one prepared) := by
  constructor
  · simpa [initialVPowers] using hone
  · simpa [initialVPowers] using hprepared.value

theorem advanceVPowers_sound
    {bits n : ℕ} {prepared : VPrepared} {state : VPowerState}
    {v : ℝ} (hn : 1 ≤ n)
    (hprepared : VPreparedSound bits v prepared)
    (hstate : VPowerStateSound bits n v state) :
    VPowerStateSound bits (n + 1) v
      (advanceVPowers bits prepared state) := by
  constructor
  · have hmul := NatInterval.mul_contains
      hstate.vPowEven hprepared.vSquared
    simpa [advanceVPowers, pow_add,
      show 2 * (n + 1) - 2 = (2 * n - 2) + 2 by omega] using hmul
  · have hmul := NatInterval.mul_contains
      hstate.vPowOdd hprepared.vSquared
    simpa [advanceVPowers, pow_add,
      show 2 * (n + 1) - 1 = (2 * n - 1) + 2 by omega] using hmul

theorem uShape_contains
    {bits n : ℕ} {one : NatInterval} {prepared : VPrepared}
    {powers : VPowerState} {v : ℝ}
    (hone : one.Contains bits 1)
    (hprepared : VPreparedSound bits v prepared)
    (hpowers : VPowerStateSound bits n v powers) :
    (uShape bits one prepared powers).Contains bits
      (lrCompactVCenteredU v n) := by
  have honePlusOdd := NatInterval.add_contains hone hpowers.vPowOdd
  have hmul := NatInterval.mul_contains
    hprepared.onePlusV honePlusOdd
  simpa [uShape, lrCompactVCenteredU] using hmul

theorem uDerivativeShape_contains
    {bits n : ℕ} {one : NatInterval} {prepared : VPrepared}
    {powers : VPowerState} {v : ℝ}
    (hone : one.Contains bits 1)
    (hprepared : VPreparedSound bits v prepared)
    (hpowers : VPowerStateSound bits n v powers) :
    (uDerivativeShape bits one prepared powers n).Contains bits
      (lrCompactVCenteredUDeriv v n) := by
  let m := 2 * n - 1
  have honePlusOdd := NatInterval.add_contains hone hpowers.vPowOdd
  have hbase := NatInterval.mul_contains
    hprepared.onePlusV hpowers.vPowEven
  have hweighted := NatInterval.scaleNat_contains
    (coefficient := m) hbase
  have hadd := NatInterval.add_contains honePlusOdd hweighted
  have hvalue :
      1 + v ^ (2 * n - 1) +
          (m : ℝ) * ((1 + v) * v ^ (2 * n - 2)) =
        lrCompactVCenteredUDeriv v n := by
    unfold lrCompactVCenteredUDeriv
    dsimp only
    rw [show 2 * n - 1 - 1 = 2 * n - 2 by omega]
    dsimp [m]
    ring
  rw [← hvalue]
  simpa [uDerivativeShape, m] using hadd

/-! ## Shared coefficient enclosure -/

/-- Soundness of the signed varying coefficient and the nonnegative
constant part of one polynomial head term. -/
structure CoefficientSound
    (bits n : ℕ) (lambda R : ℝ) (c : Coefficient) : Prop where
  a : c.a.Contains bits (lrCompactVLambdaCenteredA lambda R n)
  constantP : c.constantP.Contains bits
    (4 * lambda * (1 - lrCompactVScore R n))

theorem coefficient_sound
    {bits n : ℕ} {input : SharedInput} {R : ℝ}
    {state : CoefficientState}
    (hn : 1 ≤ n)
    (hRinput : input.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hstate : CoefficientStateSound bits n
      (rLowerValue bits input) (rUpperValue bits input) state) :
    CoefficientSound bits n (lambdaValue bits input) R
      (coefficient bits (prepareShared bits input) state) := by
  have hclamp := clampUnit_contains hRinput hRunit.1 hRunit.2
  have hlo : rLowerValue bits input ≤ R := by
    exact hclamp.1
  have hhi : R ≤ rUpperValue bits input := by
    exact hclamp.2
  have hscore := scoreInterval_contains hn
    (rLowerValue_mem_unit bits input)
    (rUpperValue_mem_unit bits input) hRunit hlo hhi hstate
  have hweighted := NatInterval.mul_contains
    (prepareShared_onePlusLambda_contains bits input) hscore
  have ha := IntInterval.sub_contains
    (IntInterval.toSigned_contains hweighted)
    (IntInterval.toSigned_contains
      (prepareShared_lambda_contains bits input))
  have hscoreComplement := oneSubUnit_contains hscore
    (lrCompactVScore_nonneg hRunit.1 hn)
    (lrCompactVScore_le_one hRunit hn)
  have hconstantBase := NatInterval.mul_contains
    (prepareShared_lambda_contains bits input) hscoreComplement
  have hconstantScaled := NatInterval.scaleNat_contains
    (coefficient := 4) hconstantBase
  constructor
  · simpa [coefficient, lrCompactVLambdaCenteredA] using ha
  · convert IntInterval.toSigned_contains hconstantScaled using 1 <;> ring

/-! ## Per-index contributions -/

theorem coefficientDenominator_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < coefficientDenominator n := by
  unfold coefficientDenominator
  exact Nat.mul_pos (by omega) (by omega)

theorem xDerivativeDenominator_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < xDerivativeDenominator n := by
  unfold xDerivativeDenominator
  omega

theorem lrLowA_eq_one_div_coefficientDenominator
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowA n = 1 / (coefficientDenominator n : ℝ) := by
  unfold lrLowA coefficientDenominator
  norm_num only [Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (show 1 ≤ 2 * n by omega), Nat.cast_one]

theorem lrLowA_mul_nat_eq_one_div_xDerivativeDenominator
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowA n * (n : ℝ) =
      1 / (xDerivativeDenominator n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnROne : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hodd : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
    nlinarith
  unfold lrLowA xDerivativeDenominator
  norm_num only [Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (show 1 ≤ 2 * n by omega), Nat.cast_one]
  field_simp [hnR.ne', hodd.ne'] <;> ring

theorem lrLowA_mul_nat_mul_pred_eq
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowA n * ((n * (n - 1) : ℕ) : ℝ) =
      ((n - 1 : ℕ) : ℝ) /
        (xDerivativeDenominator n : ℝ) := by
  rw [Nat.cast_mul, ← mul_assoc,
    lrLowA_mul_nat_eq_one_div_xDerivativeDenominator hn]
  ring

theorem signedMulTwoNonnegative_contains
    {bits : ℕ} {signed : IntInterval} {first second : NatInterval}
    {x y z : ℝ}
    (hx : signed.Contains bits x)
    (hy : first.Contains bits y) (hz : second.Contains bits z) :
    (signedMulTwoNonnegative bits signed first second).Contains bits
      (x * y * z) := by
  exact IntInterval.mulNonnegative_contains
    (IntInterval.mulNonnegative_contains hx hy) hz

theorem pContribution_contains
    {bits n : ℕ} {c : Coefficient} {powers : XPowerState}
    {u : NatInterval} {lambda R x v : ℝ}
    (hn : 1 ≤ n)
    (hc : CoefficientSound bits n lambda R c)
    (hpowers : XPowerStateSound bits n x powers)
    (hu : u.Contains bits (lrCompactVCenteredU v n)) :
    (pContribution bits n c powers u).Contains bits
      (lrCompactVLambdaCenteredPolynomialTerm lambda R v x n) := by
  have hvary := signedMulTwoNonnegative_contains
    hc.a hpowers.xPow hu
  have hsum := IntInterval.add_contains hvary hc.constantP
  have hdiv := IntInterval.divNat_contains
    (coefficientDenominator_pos hn) hsum
  have hdiv' :
      (pContribution bits n c powers u).Contains bits
        ((lrCompactVLambdaCenteredA lambda R n * x ^ n *
              lrCompactVCenteredU v n +
            4 * lambda * (1 - lrCompactVScore R n)) /
          (coefficientDenominator n : ℝ)) := by
    simpa [pContribution] using hdiv
  convert hdiv' using 1
  unfold lrCompactVLambdaCenteredPolynomialTerm
  rw [lrLowA_eq_one_div_coefficientDenominator hn]
  ring

theorem pvContribution_contains
    {bits n : ℕ} {c : Coefficient} {powers : XPowerState}
    {uDeriv : NatInterval} {lambda R x v : ℝ}
    (hn : 1 ≤ n)
    (hc : CoefficientSound bits n lambda R c)
    (hpowers : XPowerStateSound bits n x powers)
    (huDeriv : uDeriv.Contains bits
      (lrCompactVCenteredUDeriv v n)) :
    (pvContribution bits n c powers uDeriv).Contains bits
      (lrCompactVLambdaCenteredPolynomialTermV lambda R v x n) := by
  have hraw := signedMulTwoNonnegative_contains
    hc.a hpowers.xPow huDeriv
  have hdiv := IntInterval.divNat_contains
    (coefficientDenominator_pos hn) hraw
  have hdiv' :
      (pvContribution bits n c powers uDeriv).Contains bits
        ((lrCompactVLambdaCenteredA lambda R n * x ^ n *
            lrCompactVCenteredUDeriv v n) /
          (coefficientDenominator n : ℝ)) := by
    simpa [pvContribution] using hdiv
  convert hdiv' using 1
  unfold lrCompactVLambdaCenteredPolynomialTermV
  rw [lrLowA_eq_one_div_coefficientDenominator hn]
  ring

theorem pxContribution_contains
    {bits n : ℕ} {c : Coefficient} {powers : XPowerState}
    {u : NatInterval} {lambda R x v : ℝ}
    (hn : 1 ≤ n)
    (hc : CoefficientSound bits n lambda R c)
    (hpowers : XPowerStateSound bits n x powers)
    (hu : u.Contains bits (lrCompactVCenteredU v n)) :
    (pxContribution bits n c powers u).Contains bits
      (lrCompactVLambdaCenteredPolynomialTermX lambda R v x n) := by
  have hraw := signedMulTwoNonnegative_contains
    hc.a hpowers.xPowPrev hu
  have hdiv := IntInterval.divNat_contains
    (xDerivativeDenominator_pos hn) hraw
  have hdiv' :
      (pxContribution bits n c powers u).Contains bits
        ((lrCompactVLambdaCenteredA lambda R n * x ^ (n - 1) *
            lrCompactVCenteredU v n) /
          (xDerivativeDenominator n : ℝ)) := by
    simpa [pxContribution] using hdiv
  have heq :
      (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 1) *
          lrCompactVCenteredU v n) /
          (xDerivativeDenominator n : ℝ) =
        lrCompactVLambdaCenteredPolynomialTermX lambda R v x n := by
    unfold lrCompactVLambdaCenteredPolynomialTermX
    calc
      _ = (1 / (xDerivativeDenominator n : ℝ)) *
          (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 1) *
            lrCompactVCenteredU v n) := by ring
      _ = (lrLowA n * (n : ℝ)) *
          (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 1) *
            lrCompactVCenteredU v n) := by
          rw [lrLowA_mul_nat_eq_one_div_xDerivativeDenominator hn]
      _ = _ := by ring
  rw [← heq]
  exact hdiv'

theorem pxxContribution_contains
    {bits n : ℕ} {c : Coefficient} {powers : XPowerState}
    {u : NatInterval} {lambda R x v : ℝ}
    (hn : 1 ≤ n)
    (hc : CoefficientSound bits n lambda R c)
    (hpowers : XPowerStateSound bits n x powers)
    (hu : u.Contains bits (lrCompactVCenteredU v n)) :
    (pxxContribution bits n c powers u).Contains bits
      (lrCompactVLambdaCenteredPolynomialTermXX lambda R v x n) := by
  have hraw := signedMulTwoNonnegative_contains
    hc.a hpowers.xPowPrevPrev hu
  have hscaled := IntInterval.scaleNat_contains
    (coefficient := n - 1) hraw
  have hdiv := IntInterval.divNat_contains
    (xDerivativeDenominator_pos hn) hscaled
  have hdiv' :
      (pxxContribution bits n c powers u).Contains bits
        (((n - 1 : ℕ) : ℝ) *
          (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 2) *
            lrCompactVCenteredU v n) /
          (xDerivativeDenominator n : ℝ)) := by
    simpa [pxxContribution] using hdiv
  have heq :
      ((n - 1 : ℕ) : ℝ) *
          (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 2) *
            lrCompactVCenteredU v n) /
          (xDerivativeDenominator n : ℝ) =
        lrCompactVLambdaCenteredPolynomialTermXX lambda R v x n := by
    unfold lrCompactVLambdaCenteredPolynomialTermXX
    calc
      _ = (((n - 1 : ℕ) : ℝ) /
          (xDerivativeDenominator n : ℝ)) *
            (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 2) *
              lrCompactVCenteredU v n) := by ring
      _ = (lrLowA n * ((n * (n - 1) : ℕ) : ℝ)) *
            (lrCompactVLambdaCenteredA lambda R n * x ^ (n - 2) *
              lrCompactVCenteredU v n) := by
          rw [lrLowA_mul_nat_mul_pred_eq hn]
      _ = _ := by ring
  rw [← heq]
  exact hdiv'

/-! The derivative heads are named locally so the loop invariants and the
finishing identities stay small. -/

noncomputable def polynomialVHead
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrCompactVLambdaCenteredPolynomialTermV lambda R v x (j + 1)

noncomputable def polynomialXHead
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrCompactVLambdaCenteredPolynomialTermX lambda R v x (j + 1)

noncomputable def polynomialXXHead
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrCompactVLambdaCenteredPolynomialTermXX lambda R v x (j + 1)

/-! ## Fused monotone-corner loop -/

theorem prepareShared_one_contains (bits : ℕ) (input : SharedInput) :
    (prepareShared bits input).one.Contains bits 1 := by
  simpa [prepareShared] using NatInterval.one_contains bits

theorem prepareMonotoneCorner_topV_sound
    {bits : ℕ} {input : MonotoneCornerInput} {v : ℝ}
    (hv : input.vHi.Contains bits v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    VPreparedSound bits v (prepareMonotoneCorner bits input).topV := by
  simpa [prepareMonotoneCorner] using
    prepareV_sound (prepareShared_one_contains bits input.shared)
      hv hv0 hv1

theorem prepareMonotoneCorner_fullV_sound
    {bits : ℕ} {input : MonotoneCornerInput} {v : ℝ}
    (hv : input.vFull.Contains bits v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    VPreparedSound bits v (prepareMonotoneCorner bits input).fullV := by
  simpa [prepareMonotoneCorner] using
    prepareV_sound (prepareShared_one_contains bits input.shared)
      hv hv0 hv1

theorem prepareMonotoneCorner_topX_sound
    {bits : ℕ} {input : MonotoneCornerInput} {x : ℝ}
    (hx : input.xHi.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    XPreparedSound bits x (prepareMonotoneCorner bits input).topX := by
  simpa [prepareMonotoneCorner] using prepareX_sound hx hx0 hx1

theorem prepareMonotoneCorner_fullX_sound
    {bits : ℕ} {input : MonotoneCornerInput} {x : ℝ}
    (hx : input.xFull.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    XPreparedSound bits x (prepareMonotoneCorner bits input).fullX := by
  simpa [prepareMonotoneCorner] using prepareX_sound hx hx0 hx1

/-- Full semantic invariant after `terms` iterations of the corner loop. -/
structure MonotoneCornerStateSound
    (bits terms : ℕ) (input : MonotoneCornerInput)
    (R vTop xTop vFull xFull : ℝ)
    (state : MonotoneCornerState) : Prop where
  coefficient : CoefficientStateSound bits (terms + 1)
    (rLowerValue bits input.shared) (rUpperValue bits input.shared)
    state.coefficient
  topVPowers : VPowerStateSound bits (terms + 1) vTop state.topVPowers
  fullVPowers : VPowerStateSound bits (terms + 1) vFull state.fullVPowers
  topXPowers : XPowerStateSound bits (terms + 1) xTop state.topXPowers
  fullXPowers : XPowerStateSound bits (terms + 1) xFull state.fullXPowers
  pHead : state.pHead.Contains bits
    (lrCompactVLambdaCenteredPolynomialHead terms
      (lambdaValue bits input.shared) R vTop xTop)
  pvHead : state.pvHead.Contains bits
    (polynomialVHead terms (lambdaValue bits input.shared) R vFull xFull)
  pxHead : state.pxHead.Contains bits
    (polynomialXHead terms (lambdaValue bits input.shared) R vTop xFull)

theorem initialMonotoneCornerState_sound
    {bits : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ}
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxTop : input.xHi.Contains bits xTop)
    (hxTop0 : 0 ≤ xTop) (hxTop1 : xTop ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1) :
    MonotoneCornerStateSound bits 0 input R vTop xTop vFull xFull
      (initialMonotoneCornerState (prepareMonotoneCorner bits input)) := by
  have hone := prepareShared_one_contains bits input.shared
  have htopV := prepareMonotoneCorner_topV_sound
    hvTop hvTop0 hvTop1
  have hfullV := prepareMonotoneCorner_fullV_sound
    hvFull hvFull0 hvFull1
  have htopX := prepareMonotoneCorner_topX_sound
    hxTop hxTop0 hxTop1
  have hfullX := prepareMonotoneCorner_fullX_sound
    hxFull hxFull0 hxFull1
  constructor
  · simpa [initialMonotoneCornerState, prepareMonotoneCorner] using
      initialCoefficientState_sound bits input.shared
  · simpa [initialMonotoneCornerState, prepareMonotoneCorner] using
      initialVPowers_sound hone htopV
  · simpa [initialMonotoneCornerState, prepareMonotoneCorner] using
      initialVPowers_sound hone hfullV
  · simpa [initialMonotoneCornerState, prepareMonotoneCorner] using
      initialXPowers_sound hone htopX
  · simpa [initialMonotoneCornerState, prepareMonotoneCorner] using
      initialXPowers_sound hone hfullX
  · simpa [initialMonotoneCornerState,
      lrCompactVLambdaCenteredPolynomialHead] using
      IntInterval.zero_contains bits
  · simpa [initialMonotoneCornerState, polynomialVHead] using
      IntInterval.zero_contains bits
  · simpa [initialMonotoneCornerState, polynomialXHead] using
      IntInterval.zero_contains bits

theorem monotoneCornerStep_sound
    {bits terms : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ} {state : MonotoneCornerState}
    (hR : input.shared.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxTop : input.xHi.Contains bits xTop)
    (hxTop0 : 0 ≤ xTop) (hxTop1 : xTop ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1)
    (hstate : MonotoneCornerStateSound bits terms input
      R vTop xTop vFull xFull state) :
    MonotoneCornerStateSound bits (terms + 1) input
      R vTop xTop vFull xFull
      (monotoneCornerStep bits (prepareMonotoneCorner bits input)
        (terms + 1) state) := by
  have hn : 1 ≤ terms + 1 := by omega
  have hone := prepareShared_one_contains bits input.shared
  have htopV := prepareMonotoneCorner_topV_sound
    hvTop hvTop0 hvTop1
  have hfullV := prepareMonotoneCorner_fullV_sound
    hvFull hvFull0 hvFull1
  have htopX := prepareMonotoneCorner_topX_sound
    hxTop hxTop0 hxTop1
  have hfullX := prepareMonotoneCorner_fullX_sound
    hxFull hxFull0 hxFull1
  have hc : CoefficientSound bits (terms + 1)
      (lambdaValue bits input.shared) R
      (coefficient bits (prepareMonotoneCorner bits input).shared
        state.coefficient) := by
    simpa [prepareMonotoneCorner] using
      coefficient_sound hn hR hRunit hstate.coefficient
  have htopU := uShape_contains hone htopV hstate.topVPowers
  have hfullUDeriv := uDerivativeShape_contains
    hone hfullV hstate.fullVPowers
  have hpTerm := pContribution_contains hn hc
    hstate.topXPowers htopU
  have hpvTerm := pvContribution_contains hn hc
    hstate.fullXPowers hfullUDeriv
  have hpxTerm := pxContribution_contains hn hc
    hstate.fullXPowers htopU
  constructor
  · simpa [monotoneCornerStep, prepareMonotoneCorner,
      show terms + 1 + 1 = (terms + 1) + 1 by rfl] using
      advanceCoefficient_sound hn hstate.coefficient
  · simpa [monotoneCornerStep,
      show terms + 1 + 1 = (terms + 1) + 1 by rfl] using
      advanceVPowers_sound hn htopV hstate.topVPowers
  · simpa [monotoneCornerStep,
      show terms + 1 + 1 = (terms + 1) + 1 by rfl] using
      advanceVPowers_sound hn hfullV hstate.fullVPowers
  · simpa [monotoneCornerStep,
      show terms + 1 + 1 = (terms + 1) + 1 by rfl] using
      advanceXPowers_sound hn htopX hstate.topXPowers
  · simpa [monotoneCornerStep,
      show terms + 1 + 1 = (terms + 1) + 1 by rfl] using
      advanceXPowers_sound hn hfullX hstate.fullXPowers
  · simpa [monotoneCornerStep,
      lrCompactVLambdaCenteredPolynomialHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pHead hpTerm
  · simpa [monotoneCornerStep, polynomialVHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pvHead hpvTerm
  · simpa [monotoneCornerStep, polynomialXHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pxHead hpxTerm

theorem runMonotoneCorner_sound
    {bits : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ}
    (hR : input.shared.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxTop : input.xHi.Contains bits xTop)
    (hxTop0 : 0 ≤ xTop) (hxTop1 : xTop ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1) :
    ∀ terms,
      MonotoneCornerStateSound bits terms input R vTop xTop vFull xFull
        (runMonotoneCorner bits (prepareMonotoneCorner bits input) terms)
  | 0 => initialMonotoneCornerState_sound
      hvTop hvTop0 hvTop1 hxTop hxTop0 hxTop1
      hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1
  | terms + 1 => by
      simpa [runMonotoneCorner] using monotoneCornerStep_sound
        hR hRunit hvTop hvTop0 hvTop1 hxTop hxTop0 hxTop1
        hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1
        (runMonotoneCorner_sound hR hRunit
          hvTop hvTop0 hvTop1 hxTop hxTop0 hxTop1
          hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1 terms)

/-- The three real functions enclosed by one completed corner evaluation. -/
structure MonotoneCornerOutputSound
    (bits terms : ℕ) (input : MonotoneCornerInput)
    (R vTop xTop vFull xFull : ℝ)
    (output : MonotoneCornerOutput) : Prop where
  p : output.p.Contains bits
    (lrCompactVLambdaCenteredPolynomialFinite terms
      (lambdaValue bits input.shared) R vTop xTop)
  pv : output.pv.Contains bits
    (lrCompactVLambdaCenteredPolynomialV terms
      (lambdaValue bits input.shared) R vFull xFull)
  px : output.px.Contains bits
    (lrCompactVLambdaCenteredPolynomialX terms
      (lambdaValue bits input.shared) R vTop xFull)

theorem finishMonotoneCorner_sound
    {bits terms : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ} {state : MonotoneCornerState}
    (hw : input.shared.wOne.Contains bits (lrWKernel R 1))
    (htopV : VPreparedSound bits vTop
      (prepareMonotoneCorner bits input).topV)
    (htopX : XPreparedSound bits xTop
      (prepareMonotoneCorner bits input).topX)
    (hfullX : XPreparedSound bits xFull
      (prepareMonotoneCorner bits input).fullX)
    (hstate : MonotoneCornerStateSound bits terms input
      R vTop xTop vFull xFull state) :
    MonotoneCornerOutputSound bits terms input R vTop xTop vFull xFull
      (finishMonotoneCorner bits (prepareMonotoneCorner bits input) state) := by
  have hw' : (prepareMonotoneCorner bits input).shared.wOne.Contains bits
      (lrWKernel R 1) := by
    simpa [prepareMonotoneCorner, prepareShared] using hw
  have hvw := NatInterval.mul_contains htopV.value hw'
  have hvwx := NatInterval.mul_contains hvw htopX.value
  have hpEnd := IntInterval.toSigned_contains
    (NatInterval.scaleNat_contains (coefficient := 4) hvwx)
  have hpxEnd := IntInterval.toSigned_contains
    (NatInterval.scaleNat_contains (coefficient := 4) hvw)
  have hxw := NatInterval.mul_contains hfullX.value hw'
  have hpvEnd := IntInterval.toSigned_contains
    (NatInterval.scaleNat_contains (coefficient := 4) hxw)
  have hpEnd' :
      (((((prepareMonotoneCorner bits input).topV.v.mul bits
          (prepareMonotoneCorner bits input).shared.wOne).mul bits
          (prepareMonotoneCorner bits input).topX.x).scaleNat 4).toSigned).Contains
        bits (4 * vTop * xTop * lrWKernel R 1) := by
    convert hpEnd using 1 <;> ring
  have hpvEnd' :
      ((((prepareMonotoneCorner bits input).fullX.x.mul bits
          (prepareMonotoneCorner bits input).shared.wOne).scaleNat 4).toSigned).Contains
        bits (4 * xFull * lrWKernel R 1) := by
    convert hpvEnd using 1 <;> ring
  have hpxEnd' :
      ((((prepareMonotoneCorner bits input).topV.v.mul bits
          (prepareMonotoneCorner bits input).shared.wOne).scaleNat 4).toSigned).Contains
        bits (4 * vTop * lrWKernel R 1) := by
    convert hpxEnd using 1 <;> ring
  constructor
  · simpa [finishMonotoneCorner,
      lrCompactVLambdaCenteredPolynomialFinite] using
      IntInterval.sub_contains hstate.pHead hpEnd'
  · simpa [finishMonotoneCorner, pvEndpoint, polynomialVHead,
      lrCompactVLambdaCenteredPolynomialV] using
      IntInterval.sub_contains hstate.pvHead hpvEnd'
  · simpa [finishMonotoneCorner, polynomialXHead,
      lrCompactVLambdaCenteredPolynomialX] using
      IntInterval.sub_contains hstate.pxHead hpxEnd'

theorem evalMonotoneCorner_sound
    {bits terms : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ}
    (hR : input.shared.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hw : input.shared.wOne.Contains bits (lrWKernel R 1))
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxTop : input.xHi.Contains bits xTop)
    (hxTop0 : 0 ≤ xTop) (hxTop1 : xTop ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1) :
    MonotoneCornerOutputSound bits terms input R vTop xTop vFull xFull
      (evalMonotoneCorner bits terms input) := by
  have htopV := prepareMonotoneCorner_topV_sound
    hvTop hvTop0 hvTop1
  have htopX := prepareMonotoneCorner_topX_sound
    hxTop hxTop0 hxTop1
  have hfullX := prepareMonotoneCorner_fullX_sound
    hxFull hxFull0 hxFull1
  have hrun := runMonotoneCorner_sound hR hRunit
    hvTop hvTop0 hvTop1 hxTop hxTop0 hxTop1
    hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1 terms
  simpa [evalMonotoneCorner] using
    finishMonotoneCorner_sound hw htopV htopX hfullX hrun

theorem MonotoneCornerOutputSound.valueLower_le
    {bits terms : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ} {output : MonotoneCornerOutput}
    (houtput : MonotoneCornerOutputSound bits terms input
      R vTop xTop vFull xFull output) :
    (decodeInt bits output.observe.valueLower : ℝ) ≤
      lrCompactVLambdaCenteredPolynomialFinite terms
        (lambdaValue bits input.shared) R vTop xTop := by
  simpa [MonotoneCornerOutput.observe] using houtput.p.1

theorem MonotoneCornerOutputSound.vDerivative_le_upper
    {bits terms : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ} {output : MonotoneCornerOutput}
    (houtput : MonotoneCornerOutputSound bits terms input
      R vTop xTop vFull xFull output) :
    lrCompactVLambdaCenteredPolynomialV terms
        (lambdaValue bits input.shared) R vFull xFull ≤
      (decodeInt bits output.observe.vDerivativeUpper : ℝ) := by
  simpa [MonotoneCornerOutput.observe] using houtput.pv.2

theorem MonotoneCornerOutputSound.xDerivative_le_upper
    {bits terms : ℕ} {input : MonotoneCornerInput}
    {R vTop xTop vFull xFull : ℝ} {output : MonotoneCornerOutput}
    (houtput : MonotoneCornerOutputSound bits terms input
      R vTop xTop vFull xFull output) :
    lrCompactVLambdaCenteredPolynomialX terms
        (lambdaValue bits input.shared) R vTop xFull ≤
      (decodeInt bits output.observe.xDerivativeUpper : ℝ) := by
  simpa [MonotoneCornerOutput.observe] using houtput.px.2

/-! ## Fused monotone-convex tangent loop -/

theorem prepareMonotoneTangent_topV_sound
    {bits : ℕ} {input : MonotoneTangentInput} {v : ℝ}
    (hv : input.vHi.Contains bits v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    VPreparedSound bits v (prepareMonotoneTangent bits input).topV := by
  simpa [prepareMonotoneTangent] using
    prepareV_sound (prepareShared_one_contains bits input.shared)
      hv hv0 hv1

theorem prepareMonotoneTangent_fullV_sound
    {bits : ℕ} {input : MonotoneTangentInput} {v : ℝ}
    (hv : input.vFull.Contains bits v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    VPreparedSound bits v (prepareMonotoneTangent bits input).fullV := by
  simpa [prepareMonotoneTangent] using
    prepareV_sound (prepareShared_one_contains bits input.shared)
      hv hv0 hv1

theorem prepareMonotoneTangent_centerX_sound
    {bits : ℕ} {input : MonotoneTangentInput} {x : ℝ}
    (hx : input.xCenter.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    XPreparedSound bits x (prepareMonotoneTangent bits input).centerX := by
  simpa [prepareMonotoneTangent] using prepareX_sound hx hx0 hx1

theorem prepareMonotoneTangent_fullX_sound
    {bits : ℕ} {input : MonotoneTangentInput} {x : ℝ}
    (hx : input.xFull.Contains bits x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    XPreparedSound bits x (prepareMonotoneTangent bits input).fullX := by
  simpa [prepareMonotoneTangent] using prepareX_sound hx hx0 hx1

/-- Full semantic invariant after `terms` iterations of the tangent loop. -/
structure MonotoneTangentStateSound
    (bits terms : ℕ) (input : MonotoneTangentInput)
    (R vTop xCenter vFull xFull : ℝ)
    (state : MonotoneTangentState) : Prop where
  coefficient : CoefficientStateSound bits (terms + 1)
    (rLowerValue bits input.shared) (rUpperValue bits input.shared)
    state.coefficient
  topVPowers : VPowerStateSound bits (terms + 1) vTop state.topVPowers
  fullVPowers : VPowerStateSound bits (terms + 1) vFull state.fullVPowers
  centerXPowers : XPowerStateSound bits (terms + 1) xCenter
    state.centerXPowers
  fullXPowers : XPowerStateSound bits (terms + 1) xFull state.fullXPowers
  pHead : state.pHead.Contains bits
    (lrCompactVLambdaCenteredPolynomialHead terms
      (lambdaValue bits input.shared) R vTop xCenter)
  pvHead : state.pvHead.Contains bits
    (polynomialVHead terms (lambdaValue bits input.shared) R vFull xFull)
  pxHead : state.pxHead.Contains bits
    (polynomialXHead terms (lambdaValue bits input.shared) R vTop xCenter)
  pxxHead : state.pxxHead.Contains bits
    (polynomialXXHead terms (lambdaValue bits input.shared) R vTop xFull)

theorem initialMonotoneTangentState_sound
    {bits : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ}
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxCenter : input.xCenter.Contains bits xCenter)
    (hxCenter0 : 0 ≤ xCenter) (hxCenter1 : xCenter ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1) :
    MonotoneTangentStateSound bits 0 input R vTop xCenter vFull xFull
      (initialMonotoneTangentState (prepareMonotoneTangent bits input)) := by
  have hone := prepareShared_one_contains bits input.shared
  have htopV := prepareMonotoneTangent_topV_sound
    hvTop hvTop0 hvTop1
  have hfullV := prepareMonotoneTangent_fullV_sound
    hvFull hvFull0 hvFull1
  have hcenterX := prepareMonotoneTangent_centerX_sound
    hxCenter hxCenter0 hxCenter1
  have hfullX := prepareMonotoneTangent_fullX_sound
    hxFull hxFull0 hxFull1
  constructor
  · simpa [initialMonotoneTangentState, prepareMonotoneTangent] using
      initialCoefficientState_sound bits input.shared
  · simpa [initialMonotoneTangentState, prepareMonotoneTangent] using
      initialVPowers_sound hone htopV
  · simpa [initialMonotoneTangentState, prepareMonotoneTangent] using
      initialVPowers_sound hone hfullV
  · simpa [initialMonotoneTangentState, prepareMonotoneTangent] using
      initialXPowers_sound hone hcenterX
  · simpa [initialMonotoneTangentState, prepareMonotoneTangent] using
      initialXPowers_sound hone hfullX
  · simpa [initialMonotoneTangentState,
      lrCompactVLambdaCenteredPolynomialHead] using
      IntInterval.zero_contains bits
  · simpa [initialMonotoneTangentState, polynomialVHead] using
      IntInterval.zero_contains bits
  · simpa [initialMonotoneTangentState, polynomialXHead] using
      IntInterval.zero_contains bits
  · simpa [initialMonotoneTangentState, polynomialXXHead] using
      IntInterval.zero_contains bits

theorem monotoneTangentStep_sound
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ} {state : MonotoneTangentState}
    (hR : input.shared.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxCenter : input.xCenter.Contains bits xCenter)
    (hxCenter0 : 0 ≤ xCenter) (hxCenter1 : xCenter ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1)
    (hstate : MonotoneTangentStateSound bits terms input
      R vTop xCenter vFull xFull state) :
    MonotoneTangentStateSound bits (terms + 1) input
      R vTop xCenter vFull xFull
      (monotoneTangentStep bits (prepareMonotoneTangent bits input)
        (terms + 1) state) := by
  have hn : 1 ≤ terms + 1 := by omega
  have hone := prepareShared_one_contains bits input.shared
  have htopV := prepareMonotoneTangent_topV_sound
    hvTop hvTop0 hvTop1
  have hfullV := prepareMonotoneTangent_fullV_sound
    hvFull hvFull0 hvFull1
  have hcenterX := prepareMonotoneTangent_centerX_sound
    hxCenter hxCenter0 hxCenter1
  have hfullX := prepareMonotoneTangent_fullX_sound
    hxFull hxFull0 hxFull1
  have hc : CoefficientSound bits (terms + 1)
      (lambdaValue bits input.shared) R
      (coefficient bits (prepareMonotoneTangent bits input).shared
        state.coefficient) := by
    simpa [prepareMonotoneTangent] using
      coefficient_sound hn hR hRunit hstate.coefficient
  have htopU := uShape_contains hone htopV hstate.topVPowers
  have hfullUDeriv := uDerivativeShape_contains
    hone hfullV hstate.fullVPowers
  have hpTerm := pContribution_contains hn hc
    hstate.centerXPowers htopU
  have hpvTerm := pvContribution_contains hn hc
    hstate.fullXPowers hfullUDeriv
  have hpxTerm := pxContribution_contains hn hc
    hstate.centerXPowers htopU
  have hpxxTerm := pxxContribution_contains hn hc
    hstate.fullXPowers htopU
  constructor
  · simpa [monotoneTangentStep, prepareMonotoneTangent] using
      advanceCoefficient_sound hn hstate.coefficient
  · simpa [monotoneTangentStep] using
      advanceVPowers_sound hn htopV hstate.topVPowers
  · simpa [monotoneTangentStep] using
      advanceVPowers_sound hn hfullV hstate.fullVPowers
  · simpa [monotoneTangentStep] using
      advanceXPowers_sound hn hcenterX hstate.centerXPowers
  · simpa [monotoneTangentStep] using
      advanceXPowers_sound hn hfullX hstate.fullXPowers
  · simpa [monotoneTangentStep,
      lrCompactVLambdaCenteredPolynomialHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pHead hpTerm
  · simpa [monotoneTangentStep, polynomialVHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pvHead hpvTerm
  · simpa [monotoneTangentStep, polynomialXHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pxHead hpxTerm
  · simpa [monotoneTangentStep, polynomialXXHead,
      Finset.sum_range_succ] using
      IntInterval.add_contains hstate.pxxHead hpxxTerm

theorem runMonotoneTangent_sound
    {bits : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ}
    (hR : input.shared.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxCenter : input.xCenter.Contains bits xCenter)
    (hxCenter0 : 0 ≤ xCenter) (hxCenter1 : xCenter ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1) :
    ∀ terms,
      MonotoneTangentStateSound bits terms input R vTop xCenter vFull xFull
        (runMonotoneTangent bits (prepareMonotoneTangent bits input) terms)
  | 0 => initialMonotoneTangentState_sound
      hvTop hvTop0 hvTop1 hxCenter hxCenter0 hxCenter1
      hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1
  | terms + 1 => by
      simpa [runMonotoneTangent] using monotoneTangentStep_sound
        hR hRunit hvTop hvTop0 hvTop1
        hxCenter hxCenter0 hxCenter1
        hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1
        (runMonotoneTangent_sound hR hRunit
          hvTop hvTop0 hvTop1 hxCenter hxCenter0 hxCenter1
          hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1 terms)

/-- The four real functions enclosed by one completed tangent evaluation. -/
structure MonotoneTangentOutputSound
    (bits terms : ℕ) (input : MonotoneTangentInput)
    (R vTop xCenter vFull xFull : ℝ)
    (output : MonotoneTangentOutput) : Prop where
  p : output.p.Contains bits
    (lrCompactVLambdaCenteredPolynomialFinite terms
      (lambdaValue bits input.shared) R vTop xCenter)
  pv : output.pv.Contains bits
    (lrCompactVLambdaCenteredPolynomialV terms
      (lambdaValue bits input.shared) R vFull xFull)
  px : output.px.Contains bits
    (lrCompactVLambdaCenteredPolynomialX terms
      (lambdaValue bits input.shared) R vTop xCenter)
  pxx : output.pxx.Contains bits
    (lrCompactVLambdaCenteredPolynomialXX terms
      (lambdaValue bits input.shared) R vTop xFull)

theorem finishMonotoneTangent_sound
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ} {state : MonotoneTangentState}
    (hw : input.shared.wOne.Contains bits (lrWKernel R 1))
    (htopV : VPreparedSound bits vTop
      (prepareMonotoneTangent bits input).topV)
    (hcenterX : XPreparedSound bits xCenter
      (prepareMonotoneTangent bits input).centerX)
    (hfullX : XPreparedSound bits xFull
      (prepareMonotoneTangent bits input).fullX)
    (hstate : MonotoneTangentStateSound bits terms input
      R vTop xCenter vFull xFull state) :
    MonotoneTangentOutputSound bits terms input R vTop xCenter vFull xFull
      (finishMonotoneTangent bits (prepareMonotoneTangent bits input) state) := by
  have hw' : (prepareMonotoneTangent bits input).shared.wOne.Contains bits
      (lrWKernel R 1) := by
    simpa [prepareMonotoneTangent, prepareShared] using hw
  have hvw := NatInterval.mul_contains htopV.value hw'
  have hvwx := NatInterval.mul_contains hvw hcenterX.value
  have hpEnd := IntInterval.toSigned_contains
    (NatInterval.scaleNat_contains (coefficient := 4) hvwx)
  have hpxEnd := IntInterval.toSigned_contains
    (NatInterval.scaleNat_contains (coefficient := 4) hvw)
  have hxw := NatInterval.mul_contains hfullX.value hw'
  have hpvEnd := IntInterval.toSigned_contains
    (NatInterval.scaleNat_contains (coefficient := 4) hxw)
  have hpEnd' :
      (((((prepareMonotoneTangent bits input).topV.v.mul bits
          (prepareMonotoneTangent bits input).shared.wOne).mul bits
          (prepareMonotoneTangent bits input).centerX.x).scaleNat 4).toSigned).Contains
        bits (4 * vTop * xCenter * lrWKernel R 1) := by
    convert hpEnd using 1 <;> ring
  have hpvEnd' :
      ((((prepareMonotoneTangent bits input).fullX.x.mul bits
          (prepareMonotoneTangent bits input).shared.wOne).scaleNat 4).toSigned).Contains
        bits (4 * xFull * lrWKernel R 1) := by
    convert hpvEnd using 1 <;> ring
  have hpxEnd' :
      ((((prepareMonotoneTangent bits input).topV.v.mul bits
          (prepareMonotoneTangent bits input).shared.wOne).scaleNat 4).toSigned).Contains
        bits (4 * vTop * lrWKernel R 1) := by
    convert hpxEnd using 1 <;> ring
  constructor
  · simpa [finishMonotoneTangent,
      lrCompactVLambdaCenteredPolynomialFinite] using
      IntInterval.sub_contains hstate.pHead hpEnd'
  · simpa [finishMonotoneTangent, pvEndpoint, polynomialVHead,
      lrCompactVLambdaCenteredPolynomialV] using
      IntInterval.sub_contains hstate.pvHead hpvEnd'
  · simpa [finishMonotoneTangent, polynomialXHead,
      lrCompactVLambdaCenteredPolynomialX] using
      IntInterval.sub_contains hstate.pxHead hpxEnd'
  · simpa [finishMonotoneTangent, polynomialXXHead,
      lrCompactVLambdaCenteredPolynomialXX] using hstate.pxxHead

theorem evalMonotoneTangent_sound
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ}
    (hR : input.shared.r.Contains bits R)
    (hRunit : R ∈ Icc (0 : ℝ) 1)
    (hw : input.shared.wOne.Contains bits (lrWKernel R 1))
    (hvTop : input.vHi.Contains bits vTop)
    (hvTop0 : 0 ≤ vTop) (hvTop1 : vTop ≤ 1)
    (hxCenter : input.xCenter.Contains bits xCenter)
    (hxCenter0 : 0 ≤ xCenter) (hxCenter1 : xCenter ≤ 1)
    (hvFull : input.vFull.Contains bits vFull)
    (hvFull0 : 0 ≤ vFull) (hvFull1 : vFull ≤ 1)
    (hxFull : input.xFull.Contains bits xFull)
    (hxFull0 : 0 ≤ xFull) (hxFull1 : xFull ≤ 1) :
    MonotoneTangentOutputSound bits terms input R vTop xCenter vFull xFull
      (evalMonotoneTangent bits terms input) := by
  have htopV := prepareMonotoneTangent_topV_sound
    hvTop hvTop0 hvTop1
  have hcenterX := prepareMonotoneTangent_centerX_sound
    hxCenter hxCenter0 hxCenter1
  have hfullX := prepareMonotoneTangent_fullX_sound
    hxFull hxFull0 hxFull1
  have hrun := runMonotoneTangent_sound hR hRunit
    hvTop hvTop0 hvTop1 hxCenter hxCenter0 hxCenter1
    hvFull hvFull0 hvFull1 hxFull hxFull0 hxFull1 terms
  simpa [evalMonotoneTangent] using
    finishMonotoneTangent_sound hw htopV hcenterX hfullX hrun

theorem MonotoneTangentOutputSound.valueLower_le
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ} {output : MonotoneTangentOutput}
    (houtput : MonotoneTangentOutputSound bits terms input
      R vTop xCenter vFull xFull output) :
    (decodeInt bits output.observe.valueLower : ℝ) ≤
      lrCompactVLambdaCenteredPolynomialFinite terms
        (lambdaValue bits input.shared) R vTop xCenter := by
  simpa [MonotoneTangentOutput.observe] using houtput.p.1

theorem MonotoneTangentOutputSound.xGradient_abs_le
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ} {output : MonotoneTangentOutput}
    (houtput : MonotoneTangentOutputSound bits terms input
      R vTop xCenter vFull xFull output) :
    |lrCompactVLambdaCenteredPolynomialX terms
        (lambdaValue bits input.shared) R vTop xCenter| ≤
      (decodeNat bits output.observe.xGradientMaxAbs : ℝ) := by
  simpa [MonotoneTangentOutput.observe] using
    IntInterval.abs_le_decode_maxAbs houtput.px

theorem MonotoneTangentOutputSound.vDerivative_le_upper
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ} {output : MonotoneTangentOutput}
    (houtput : MonotoneTangentOutputSound bits terms input
      R vTop xCenter vFull xFull output) :
    lrCompactVLambdaCenteredPolynomialV terms
        (lambdaValue bits input.shared) R vFull xFull ≤
      (decodeInt bits output.observe.vDerivativeUpper : ℝ) := by
  simpa [MonotoneTangentOutput.observe] using houtput.pv.2

theorem MonotoneTangentOutputSound.xSecondDerivativeLower_le
    {bits terms : ℕ} {input : MonotoneTangentInput}
    {R vTop xCenter vFull xFull : ℝ} {output : MonotoneTangentOutput}
    (houtput : MonotoneTangentOutputSound bits terms input
      R vTop xCenter vFull xFull output) :
    (decodeInt bits output.observe.xSecondDerivativeLower : ℝ) ≤
      lrCompactVLambdaCenteredPolynomialXX terms
        (lambdaValue bits input.shared) R vTop xFull := by
  simpa [MonotoneTangentOutput.observe] using houtput.pxx.1

end LRCompactVCenteredMonotoneEval
end CourtadeKumar
