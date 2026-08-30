import InformationTheory.CourtadeKumar.LRDeterminantFastQPointCertificate

/-!
# Uniform success of the fast upper-`K` point certificates

The authenticated point workload uses arguments in the single rational
interval

`[148137 / 549755813888, 287 / 8192]`.

This module proves once that forty-eight logarithm-normalization steps are
enough throughout that interval.  Generated point modules can consequently
apply `autoPrimeSucceeds_authenticated` after checking only their inexpensive
rational range bounds; they do not reduce the recursive success predicate at
every point.
-/

namespace CourtadeKumar

namespace RationalEnclosure

/-- The recursive logarithm normalizer succeeds on the part of its dyadic
range below two.  This is the only part needed by probability intervals. -/
theorem autoLogRangeCertificateSucceeds_of_dyadic_bounds
    (fuel : ℕ) (x : ℚ)
    (hlower : (1 / 2 : ℚ) ^ fuel ≤ x)
    (hupper : x < 2) :
    autoLogRangeCertificateSucceeds fuel x = true := by
  induction fuel generalizing x with
  | zero =>
      simpa [autoLogRangeCertificateSucceeds] using
        (show (1 : ℚ) ≤ x ∧ x < 2 by simpa using And.intro hlower hupper)
  | succ fuel ih =>
      by_cases hxLower : x < 1
      · simp only [autoLogRangeCertificateSucceeds, hxLower, if_pos]
        apply ih (2 * x)
        · rw [pow_succ] at hlower
          norm_num at hlower ⊢
          nlinarith
        · nlinarith
      · simp [autoLogRangeCertificateSucceeds, hxLower, hupper]

/-- An ordered rational interval contained in the dyadic fuel range has a
successful automatically generated logarithm interval certificate. -/
theorem autoLogIntervalCertificateSucceeds_of_dyadic_bounds
    (fuel : ℕ) (input : RationalEnclosure)
    (hlower : (1 / 2 : ℚ) ^ fuel ≤ input.lower)
    (hordered : input.lower ≤ input.upper)
    (hupper : input.upper < 2) :
    autoLogIntervalCertificateSucceeds fuel input = true := by
  simp only [autoLogIntervalCertificateSucceeds, Bool.and_eq_true,
    decide_eq_true_eq]
  have hhalfPositive : (0 : ℚ) < (1 / 2 : ℚ) ^ fuel := by positivity
  exact ⟨hhalfPositive.trans_le hlower,
    autoLogRangeCertificateSucceeds_of_dyadic_bounds fuel input.lower
      hlower (hordered.trans_lt hupper),
    autoLogRangeCertificateSucceeds_of_dyadic_bounds fuel input.upper
      (hlower.trans hordered) hupper⟩

end RationalEnclosure

namespace LRQFastPointCertificate

private theorem lowerProbability_lower (logFuel : ℕ) (y : ℚ) :
    (auto logFuel y).lowerProbability.lower = (1 - sqrtUpper y) / 2 := by
  norm_num [auto, LRQPointCertificate.lowerProbability,
    LRQPointCertificate.sqrtEnclosure, sqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.sub, RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem lowerProbability_upper (logFuel : ℕ) (y : ℚ) :
    (auto logFuel y).lowerProbability.upper = (1 - sqrtLower y) / 2 := by
  norm_num [auto, LRQPointCertificate.lowerProbability,
    LRQPointCertificate.sqrtEnclosure, sqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.sub, RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem upperProbability_lower (logFuel : ℕ) (y : ℚ) :
    (auto logFuel y).upperProbability.lower = (1 + sqrtLower y) / 2 := by
  norm_num [auto, LRQPointCertificate.upperProbability,
    LRQPointCertificate.sqrtEnclosure, sqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem upperProbability_upper (logFuel : ℕ) (y : ℚ) :
    (auto logFuel y).upperProbability.upper = (1 + sqrtUpper y) / 2 := by
  norm_num [auto, LRQPointCertificate.upperProbability,
    LRQPointCertificate.sqrtEnclosure, sqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem sqrtUpper_le_linear {y : ℚ} (hy0 : 0 ≤ y) :
    sqrtUpper y ≤ 1 - y / 2 := by
  have h2 : 0 ≤ y ^ 2 := pow_nonneg hy0 _
  have h3 : 0 ≤ y ^ 3 := pow_nonneg hy0 _
  have h4 : 0 ≤ y ^ 4 := pow_nonneg hy0 _
  have h5 : 0 ≤ y ^ 5 := pow_nonneg hy0 _
  have h6 : 0 ≤ y ^ 6 := pow_nonneg hy0 _
  unfold sqrtUpper
  nlinarith

private theorem sqrtLower_le_sqrtUpper {y : ℚ} (hy0 : 0 ≤ y) :
    sqrtLower y ≤ sqrtUpper y := by
  unfold sqrtLower
  have h7 : 0 ≤ y ^ 7 := pow_nonneg hy0 _
  nlinarith

private theorem sqrtLower_ge_half {y : ℚ} (hy0 : 0 ≤ y)
    (hy : y ≤ 1 / 16) : 1 / 2 ≤ sqrtLower y := by
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have hpow (n : ℕ) (hn : 1 ≤ n) : y ^ n ≤ y := by
    simpa using pow_le_pow_of_le_one hy0 hy1 hn
  have h2 := hpow 2 (by omega)
  have h3 := hpow 3 (by omega)
  have h4 := hpow 4 (by omega)
  have h5 := hpow 5 (by omega)
  have h6 := hpow 6 (by omega)
  have h7 := hpow 7 (by omega)
  unfold sqrtLower sqrtUpper
  nlinarith

private theorem roundUp40_lt_add_error (x : ℚ) :
    LRUpperKDyadicOuterRounding.roundUp 40 x <
      x + 1 / (2 : ℚ) ^ 40 := by
  have hceil :
      (Int.ceil
        (x * LRUpperKDyadicOuterRounding.scale 40) : ℚ) <
        x * LRUpperKDyadicOuterRounding.scale 40 + 1 := by
    exact Int.ceil_lt_add_one _
  unfold LRUpperKDyadicOuterRounding.roundUp
  apply (div_lt_iff₀
    (LRUpperKDyadicOuterRounding.scale_pos 40)).2
  calc
    (Int.ceil (x * LRUpperKDyadicOuterRounding.scale 40) : ℚ) <
        x * LRUpperKDyadicOuterRounding.scale 40 + 1 := hceil
    _ = (x + 1 / (2 : ℚ) ^ 40) *
        LRUpperKDyadicOuterRounding.scale 40 := by
      norm_num [LRUpperKDyadicOuterRounding.scale]
      ring

private theorem roundedSqrtLower40_pos {y : ℚ}
    (hy0 : 0 ≤ y) (hy : y ≤ 1 / 16) :
    0 < LRUpperKDyadicOuterRounding.roundDown 40 (sqrtLower y) := by
  have hlower := sqrtLower_ge_half hy0 hy
  have hscaled :
      (1 : ℚ) ≤ sqrtLower y * LRUpperKDyadicOuterRounding.scale 40 := by
    have hscale :
        (2 : ℚ) ≤ LRUpperKDyadicOuterRounding.scale 40 := by
      norm_num [LRUpperKDyadicOuterRounding.scale]
    nlinarith [mul_le_mul_of_nonneg_right hlower
      (LRUpperKDyadicOuterRounding.scale_pos 40).le]
  unfold LRUpperKDyadicOuterRounding.roundDown
  apply div_pos
  · exact_mod_cast (Int.floor_pos.mpr hscaled)
  · exact LRUpperKDyadicOuterRounding.scale_pos 40

private theorem roundedLowerProbability_lower (logFuel : ℕ) (y : ℚ) :
    (roundedAuto 40 logFuel y).lowerProbability.lower =
      (1 - LRUpperKDyadicOuterRounding.roundUp 40 (sqrtUpper y)) / 2 := by
  norm_num [roundedAuto, LRQPointCertificate.lowerProbability,
    LRQPointCertificate.sqrtEnclosure, roundedSqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.sub, RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem roundedLowerProbability_upper (logFuel : ℕ) (y : ℚ) :
    (roundedAuto 40 logFuel y).lowerProbability.upper =
      (1 - LRUpperKDyadicOuterRounding.roundDown 40 (sqrtLower y)) / 2 := by
  norm_num [roundedAuto, LRQPointCertificate.lowerProbability,
    LRQPointCertificate.sqrtEnclosure, roundedSqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.sub, RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem roundedUpperProbability_lower (logFuel : ℕ) (y : ℚ) :
    (roundedAuto 40 logFuel y).upperProbability.lower =
      (1 + LRUpperKDyadicOuterRounding.roundDown 40 (sqrtLower y)) / 2 := by
  norm_num [roundedAuto, LRQPointCertificate.upperProbability,
    LRQPointCertificate.sqrtEnclosure, roundedSqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.center, RationalEnclosure.radius]
  ring

private theorem roundedUpperProbability_upper (logFuel : ℕ) (y : ℚ) :
    (roundedAuto 40 logFuel y).upperProbability.upper =
      (1 + LRUpperKDyadicOuterRounding.roundUp 40 (sqrtUpper y)) / 2 := by
  norm_num [roundedAuto, LRQPointCertificate.upperProbability,
    LRQPointCertificate.sqrtEnclosure, roundedSqrtCertificate,
    RationalEnclosure.SqrtCertificate.enclosure,
    RationalEnclosure.scale, RationalEnclosure.mul, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.center, RationalEnclosure.radius]
  ring

/-- Forty-eight range-reduction steps suffice for every fast point
certificate in the authenticated upper-`K` workload. -/
theorem autoPrimeSucceeds_authenticated {y : ℚ}
    (hyLower : 148137 / 549755813888 ≤ y)
    (hyUpper : y ≤ 287 / 8192) :
    autoPrimeSucceeds 48 y = true := by
  have hy0 : (0 : ℚ) ≤ y := by
    have : (0 : ℚ) < 148137 / 549755813888 := by norm_num
    linarith
  have hySmall : y ≤ 1 / 16 := hyUpper.trans (by norm_num)
  have hsqrtLower0 := sqrtLower_nonneg hy0 hySmall
  have hsqrtUpperLinear := sqrtUpper_le_linear hy0
  have hsqrtOrder := sqrtLower_le_sqrtUpper hy0
  have hsqrtUpper1 : sqrtUpper y ≤ 1 := by linarith
  have hdyadic : (1 / 2 : ℚ) ^ 48 ≤ y / 4 := by
    have hconstant :
        (1 / 2 : ℚ) ^ 48 ≤ (148137 / 549755813888) / 4 := by
      norm_num
    linarith
  have hceiling : (1 : ℚ) < 2 := by norm_num
  have hlowerLog :
      RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (auto 48 y).lowerProbability = true := by
    apply RationalEnclosure.autoLogIntervalCertificateSucceeds_of_dyadic_bounds
    · rw [lowerProbability_lower]
      exact hdyadic.trans (by nlinarith)
    · rw [lowerProbability_lower, lowerProbability_upper]
      linarith
    · rw [lowerProbability_upper]
      exact (show (1 - sqrtLower y) / 2 ≤ 1 by linarith).trans_lt hceiling
  have hupperLog :
      RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (auto 48 y).upperProbability = true := by
    apply RationalEnclosure.autoLogIntervalCertificateSucceeds_of_dyadic_bounds
    · rw [upperProbability_lower]
      exact hdyadic.trans (by nlinarith)
    · rw [upperProbability_lower, upperProbability_upper]
      linarith
    · rw [upperProbability_upper]
      exact (show (1 + sqrtUpper y) / 2 ≤ 1 by linarith).trans_lt hceiling
  change (
    RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (auto 48 y).lowerProbability &&
      RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (auto 48 y).upperProbability) = true
  simpa [Bool.and_eq_true] using And.intro hlowerLog hupperLog

/-- The exact rounded-polynomial scheme used by generated point modules also
succeeds uniformly.  This removes every recursive log-success reduction from
the trusted generated point proofs. -/
theorem roundedAutoPrimeSucceeds_authenticated {y : ℚ}
    (hyLower : 148137 / 549755813888 ≤ y)
    (hyUpper : y ≤ 287 / 8192) :
    roundedAutoPrimeSucceeds 40 48 y = true := by
  have hy0 : (0 : ℚ) ≤ y := by
    have : (0 : ℚ) < 148137 / 549755813888 := by norm_num
    linarith
  have hySmall : y ≤ 1 / 16 := hyUpper.trans (by norm_num)
  have hsqrtLower0 := sqrtLower_nonneg hy0 hySmall
  have hsqrtUpper0 := sqrtUpper_nonneg hy0 hySmall
  have hsqrtUpperLinear := sqrtUpper_le_linear hy0
  have hsqrtOrder := sqrtLower_le_sqrtUpper hy0
  let lowerRounded :=
    LRUpperKDyadicOuterRounding.roundDown 40 (sqrtLower y)
  let upperRounded :=
    LRUpperKDyadicOuterRounding.roundUp 40 (sqrtUpper y)
  have hlowerRounded0 : 0 ≤ lowerRounded := by
    exact LRQFastPointCertificate.roundDown_nonneg 40 hsqrtLower0
  have hlowerRoundedLe : lowerRounded ≤ sqrtLower y := by
    exact LRUpperKDyadicOuterRounding.roundDown_le 40 _
  have hupperRoundedGe : sqrtUpper y ≤ upperRounded := by
    exact LRUpperKDyadicOuterRounding.le_roundUp 40 _
  have hupperRoundedError : upperRounded < sqrtUpper y + 1 / (2 : ℚ) ^ 40 :=
    roundUp40_lt_add_error _
  have hroundedOrder : lowerRounded ≤ upperRounded :=
    hlowerRoundedLe.trans <| hsqrtOrder.trans hupperRoundedGe
  have hdyadicLower :
      (1 / 2 : ℚ) ^ 48 ≤ (1 - upperRounded) / 2 := by
    have hconstant :
        (1 / 2 : ℚ) ^ 48 ≤
          (148137 / 549755813888) / 4 - 1 / (2 : ℚ) ^ 41 := by
      norm_num
    nlinarith
  have hupperRoundedBound : upperRounded < 1 + 1 / (2 : ℚ) ^ 40 := by
    nlinarith
  have hlowerLog :
      RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (roundedAuto 40 48 y).lowerProbability = true := by
    apply RationalEnclosure.autoLogIntervalCertificateSucceeds_of_dyadic_bounds
    · rw [roundedLowerProbability_lower]
      exact hdyadicLower
    · rw [roundedLowerProbability_lower, roundedLowerProbability_upper]
      linarith
    · rw [roundedLowerProbability_upper]
      nlinarith
  have hupperLog :
      RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (roundedAuto 40 48 y).upperProbability = true := by
    apply RationalEnclosure.autoLogIntervalCertificateSucceeds_of_dyadic_bounds
    · rw [roundedUpperProbability_lower]
      have : (1 / 2 : ℚ) ^ 48 ≤ 1 / 2 := by norm_num
      nlinarith
    · rw [roundedUpperProbability_lower, roundedUpperProbability_upper]
      linarith
    · rw [roundedUpperProbability_upper]
      nlinarith
  have hsqrtPositive :
      0 < (roundedAuto 40 48 y).sqrtEnclosure.lower := by
    change 0 < lowerRounded
    exact roundedSqrtLower40_pos hy0 hySmall
  change ((
    RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (roundedAuto 40 48 y).lowerProbability &&
      RationalEnclosure.autoLogIntervalCertificateSucceeds 48
        (roundedAuto 40 48 y).upperProbability) &&
      decide ((0 : ℚ) < (roundedAuto 40 48 y).sqrtEnclosure.lower)) = true
  simpa [Bool.and_eq_true, decide_eq_true_eq] using
    And.intro (And.intro hlowerLog hupperLog) hsqrtPositive

end LRQFastPointCertificate
end CourtadeKumar
