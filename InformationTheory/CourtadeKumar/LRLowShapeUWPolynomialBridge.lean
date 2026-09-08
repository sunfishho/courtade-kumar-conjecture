import InformationTheory.CourtadeKumar.LRLowShapeUW1Power
import InformationTheory.CourtadeKumar.NativePolynomialNormalization
import InformationTheory.CourtadeKumar.LRLowShapeUW2Power
import InformationTheory.CourtadeKumar.LRLowShapeUW3Power
import InformationTheory.CourtadeKumar.LRLowShapeUW4Power
import InformationTheory.CourtadeKumar.LRLowShapeUW5Power

/-! A reusable denominator-clearing bridge for the five finite low-shape
`𝓦ₙ` certificates.  The definitions below are polynomial in `v` and `x`;
the analytic rational functions occur only in the small bridge lemmas. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowWBetaNumerator (v : ℝ) : ℝ :=
  2 * (v * (2 + v) ^ 8 + v ^ 3 * (2 + v) ^ 6 / 3 +
    v ^ 5 * (2 + v) ^ 4 / 5 + v ^ 7 * (2 + v) ^ 2 / 7 + v ^ 9 / 9)

noncomputable def lrLowWBetaDivVNumerator (v : ℝ) : ℝ :=
  2 * ((2 + v) ^ 8 + v ^ 2 * (2 + v) ^ 6 / 3 +
    v ^ 4 * (2 + v) ^ 4 / 5 + v ^ 6 * (2 + v) ^ 2 / 7 + v ^ 8 / 9)

noncomputable def lrLowWMinusLogNumerator (v : ℝ) : ℝ :=
  2 * ((1 - v) * (1 + v) ^ 8 + (1 - v) ^ 3 * (1 + v) ^ 6 / 3 +
    (1 - v) ^ 5 * (1 + v) ^ 4 / 5 +
    (1 - v) ^ 7 * (1 + v) ^ 2 / 7 + (1 - v) ^ 9 / 9)

noncomputable def lrLowWBetaUpperNumerator (v : ℝ) : ℝ :=
  lrLowWBetaNumerator v * (1 + v) + v ^ 11 / 22

noncomputable def lrLowWRadialBase (v : ℝ) : ℝ :=
  (1 + v) ^ 9 * (2 + v) ^ 9

noncomputable def lrLowWXiDenominator (v x : ℝ) : ℝ :=
  20 * (1 - v ^ 2 * x)

noncomputable def lrLowWGRadialNumerator (v : ℝ) : ℝ :=
  lrLowWBetaDivVNumerator v * (1 + v) ^ 10 +
    lrLowWMinusLogNumerator v * (2 + v) ^ 9

noncomputable def lrLowWALowerRadialNumerator (v x : ℝ) : ℝ :=
  lrLowWBetaNumerator v * (1 + v) ^ 9 +
    lrLowL12 (v ^ 2 * x) * lrLowWRadialBase v

noncomputable def lrLowWAUpperScaledNumerator (v x : ℝ) : ℝ :=
  2 * v * x * lrLowWBetaUpperNumerator v * (1 + v) ^ 7 *
      lrLowWXiDenominator v x +
    2 * v * x * lrLowL12 (v ^ 2 * x) * (1 + v) ^ 8 *
      (2 + v) ^ 9 * lrLowWXiDenominator v x +
    (20 / 13 : ℝ) * v * x * (v ^ 2 * x) ^ 13 *
      (1 + v) ^ 8 * (2 + v) ^ 9

noncomputable def lrLowWPolynomial (v x : ℝ) (n : ℕ) : ℝ :=
  lrLowH (v ^ 2 * x) n *
      (lrLowWGRadialNumerator v -
        lrLowPhiPrefix v x n * lrLowWRadialBase v -
        lrLowBnUpper n * (4 + 2 * v) * (1 + v) ^ 8 * (2 + v) ^ 9) *
      lrLowWXiDenominator v x +
    2 * (n : ℝ) * lrLowWALowerRadialNumerator v x *
      lrLowPnLower v x n * lrLowWXiDenominator v x -
    2 * (n : ℝ) * lrLowBnUpper n * lrLowWAUpperScaledNumerator v x

lemma lrLowBetaLower_mul_denominator
    {v : ℝ} (h2 : 2 + v ≠ 0) :
    lrLowBetaLower v * (2 + v) ^ 9 = lrLowWBetaNumerator v := by
  unfold lrLowBetaLower lrAtanh5 lrLowWBetaNumerator
  field_simp [h2]

lemma lrLowMinusLogLower_mul_denominator
    {v : ℝ} (h1 : 1 + v ≠ 0) :
    lrLowMinusLogLower v * (1 + v) ^ 9 =
      lrLowWMinusLogNumerator v := by
  unfold lrLowMinusLogLower lrAtanh5 lrLowWMinusLogNumerator
  field_simp [h1]

lemma lrAtanh5Upper_mul_denominator
    {v : ℝ} (h1 : 1 + v ≠ 0) (h2 : 2 + v ≠ 0) :
    lrAtanh5Upper (v / (2 + v)) * (1 + v) * (2 + v) ^ 9 =
      lrLowWBetaUpperNumerator v := by
  unfold lrAtanh5Upper lrAtanh5 lrLowWBetaUpperNumerator
    lrLowWBetaNumerator
  rw [show 1 - (v / (2 + v)) ^ 2 =
      (4 + 4 * v) / (2 + v) ^ 2 by
    field_simp [h2]
    ring]
  field_simp [h1, h2]
  ring

lemma lrLowGLower_mul_radial
    {v : ℝ} (hv : v ≠ 0) (h1 : 1 + v ≠ 0) (h2 : 2 + v ≠ 0) :
    lrLowGLower v * lrLowWRadialBase v =
      lrLowWGRadialNumerator v := by
  have hbeta := lrLowBetaLower_mul_denominator h2
  have hminus := lrLowMinusLogLower_mul_denominator h1
  have hnum : lrLowWBetaNumerator v =
      v * lrLowWBetaDivVNumerator v := by
    unfold lrLowWBetaNumerator lrLowWBetaDivVNumerator
    ring
  unfold lrLowGLower lrLowWRadialBase lrLowWGRadialNumerator
  rw [show lrLowBetaLower v = lrLowWBetaNumerator v / (2 + v) ^ 9 by
      exact (eq_div_iff (pow_ne_zero 9 h2)).2 hbeta,
    show lrLowMinusLogLower v = lrLowWMinusLogNumerator v / (1 + v) ^ 9 by
      exact (eq_div_iff (pow_ne_zero 9 h1)).2 hminus]
  rw [hnum]
  field_simp [hv, h1, h2]
  ring

lemma lrLowTailH_mul_radial
    {v : ℝ} (h1 : 1 + v ≠ 0) :
    lrLowTailH v * lrLowWRadialBase v =
      (4 + 2 * v) * (1 + v) ^ 8 * (2 + v) ^ 9 := by
  unfold lrLowTailH lrFlowM lrLowWRadialBase
  field_simp [h1]

lemma lrLowALower_mul_radial
    {v x : ℝ} (h2 : 2 + v ≠ 0) :
    lrLowALower v x * lrLowWRadialBase v =
      lrLowWALowerRadialNumerator v x := by
  have hbeta := lrLowBetaLower_mul_denominator h2
  unfold lrLowALower lrLowWRadialBase lrLowWALowerRadialNumerator
  rw [show lrLowBetaLower v = lrLowWBetaNumerator v / (2 + v) ^ 9 by
      exact (eq_div_iff (pow_ne_zero 9 h2)).2 hbeta]
  unfold lrLowWRadialBase
  field_simp [h2]

lemma lrLowAUpper_scaled_mul_base
    {v x : ℝ} (h1 : 1 + v ≠ 0) (h2 : 2 + v ≠ 0)
    (hxi : 1 - v ^ 2 * x ≠ 0) :
    lrLowAUpper v x * (2 * lrFlowM v * x) *
      lrLowWRadialBase v * lrLowWXiDenominator v x =
      lrLowWAUpperScaledNumerator v x := by
  have hupper := lrAtanh5Upper_mul_denominator h1 h2
  have hupper' : lrAtanh5Upper (v / (2 + v)) *
      ((1 + v) * (2 + v) ^ 9) = lrLowWBetaUpperNumerator v := by
    simpa [mul_assoc] using hupper
  unfold lrLowAUpper
  rw [show lrAtanh5Upper (v / (2 + v)) =
      lrLowWBetaUpperNumerator v / ((1 + v) * (2 + v) ^ 9) by
    exact (eq_div_iff (mul_ne_zero h1 (pow_ne_zero 9 h2))).2 hupper']
  unfold lrLowL12Upper lrFlowM lrLowWRadialBase
    lrLowWXiDenominator lrLowWAUpperScaledNumerator
  unfold lrLowWXiDenominator
  field_simp [h1, h2, hxi]
  ring

theorem lrLowWMinorant_mul_base_eq_polynomial
    {v x : ℝ} (hv : v ≠ 0) (h1 : 1 + v ≠ 0) (h2 : 2 + v ≠ 0)
    (hxi : 1 - v ^ 2 * x ≠ 0) (n : ℕ) :
    lrLowWMinorant v x n *
        (lrLowWRadialBase v * lrLowWXiDenominator v x) =
      lrLowWPolynomial v x n := by
  have hg := lrLowGLower_mul_radial hv h1 h2
  have hh := lrLowTailH_mul_radial h1
  have haLower := lrLowALower_mul_radial (x := x) h2
  have haUpper := lrLowAUpper_scaled_mul_base
    (x := x) h1 h2 hxi
  unfold lrLowWMinorant lrLowWPolynomial
  calc
    (lrLowH (v ^ 2 * x) n *
          (lrLowGLower v - lrLowPhiPrefix v x n -
            lrLowTailH v * lrLowBnUpper n) +
        2 * (n : ℝ) * lrLowALower v x * lrLowPnLower v x n -
        2 * (n : ℝ) * lrLowAUpper v x * (2 * lrFlowM v * x) *
          lrLowBnUpper n) *
        (lrLowWRadialBase v * lrLowWXiDenominator v x) =
      lrLowH (v ^ 2 * x) n *
          (lrLowGLower v * lrLowWRadialBase v -
            lrLowPhiPrefix v x n * lrLowWRadialBase v -
            (lrLowTailH v * lrLowWRadialBase v) * lrLowBnUpper n) *
          lrLowWXiDenominator v x +
        2 * (n : ℝ) * (lrLowALower v x * lrLowWRadialBase v) *
          lrLowPnLower v x n * lrLowWXiDenominator v x -
        2 * (n : ℝ) * lrLowBnUpper n *
          (lrLowAUpper v x * (2 * lrFlowM v * x) *
            lrLowWRadialBase v * lrLowWXiDenominator v x) := by ring
    _ = lrLowH (v ^ 2 * x) n *
          (lrLowWGRadialNumerator v -
            lrLowPhiPrefix v x n * lrLowWRadialBase v -
            lrLowBnUpper n * (4 + 2 * v) * (1 + v) ^ 8 * (2 + v) ^ 9) *
          lrLowWXiDenominator v x +
        2 * (n : ℝ) * lrLowWALowerRadialNumerator v x *
          lrLowPnLower v x n * lrLowWXiDenominator v x -
        2 * (n : ℝ) * lrLowBnUpper n * lrLowWAUpperScaledNumerator v x := by
      rw [hg, hh, haLower, haUpper]
      ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
lemma lrLowWPolynomial_one_eq_power (v z : ℝ) :
    lrLowWPolynomial v ((17 / 20 : ℝ) * z) 1 =
      lrLowW1PowerEval v z := by
  unfold lrLowWPolynomial
  unfold lrLowWGRadialNumerator lrLowWALowerRadialNumerator
    lrLowWAUpperScaledNumerator lrLowWBetaUpperNumerator
  unfold lrLowWBetaDivVNumerator lrLowWMinusLogNumerator
    lrLowWBetaNumerator lrLowWRadialBase lrLowWXiDenominator
  unfold lrLowH lrLowPhiPrefix lrLowBnUpper
    lrLowPnLower lrLowL12 lrLowT lrLowA lrLowW1PowerEval
  unfold lrLowW1VPowerEvalCol0 lrLowW1VPowerEvalCol1 lrLowW1VPowerEvalCol2 lrLowW1VPowerEvalCol3 lrLowW1VPowerEvalCol4 lrLowW1VPowerEvalCol5 lrLowW1VPowerEvalCol6 lrLowW1VPowerEvalCol7 lrLowW1VPowerEvalCol8 lrLowW1VPowerEvalCol9 lrLowW1VPowerEvalCol10 lrLowW1VPowerEvalCol11 lrLowW1VPowerEvalCol12 lrLowW1VPowerEvalCol13 lrLowW1VPowerEvalCol14 lrLowW1VPowerEvalCol15 lrLowW1VPowerEvalCol16 lrLowW1VPowerEvalCol17 lrLowW1VPowerEvalCol18 lrLowW1VPowerEvalCol19 lrLowW1VPowerEvalCol20 lrLowW1VPowerEvalCol21 lrLowW1VPowerEvalCol22 lrLowW1VPowerEvalCol23 lrLowW1VPowerEvalCol24 lrLowW1VPowerEvalCol25
  norm_num [Finset.sum_range_succ]
  ring

theorem lrLowWMinorant_one_nonneg
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) 1 := by
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have hv0 : v ≠ 0 := hv.1.ne'
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hv.1.le (sub_nonneg.mpr hv.2)]
  have hvz : v ^ 2 * z ≤ 1 := by
    calc
      v ^ 2 * z ≤ 1 * 1 := mul_le_mul hvSq hz.2 hz.1 (by norm_num)
      _ = 1 := by norm_num
  have hxiPos : 0 < 1 - v ^ 2 * ((17 / 20 : ℝ) * z) := by
    nlinarith
  have hxi : 1 - v ^ 2 * ((17 / 20 : ℝ) * z) ≠ 0 := hxiPos.ne'
  have hcertificate : 0 ≤ lrLowW1PowerEval v z := by
    rw [← lrLowW1Bernstein_eq_power]
    exact lrLowW1Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hproduct :
      0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) 1 *
        (lrLowWRadialBase v *
          lrLowWXiDenominator v ((17 / 20 : ℝ) * z)) := by
    rw [lrLowWMinorant_mul_base_eq_polynomial hv0 h1 h2 hxi,
      lrLowWPolynomial_one_eq_power]
    exact hcertificate
  have hbase : 0 < lrLowWRadialBase v *
      lrLowWXiDenominator v ((17 / 20 : ℝ) * z) := by
    have hradial : 0 < lrLowWRadialBase v := by
      unfold lrLowWRadialBase
      exact mul_pos (pow_pos (by linarith [hv.1]) _)
        (pow_pos (by linarith [hv.1]) _)
    have hden : 0 < lrLowWXiDenominator v ((17 / 20 : ℝ) * z) := by
      unfold lrLowWXiDenominator
      nlinarith
    exact mul_pos hradial hden
  exact nonneg_of_mul_nonneg_left hproduct hbase

theorem lrLowWMinorant_one_nonneg_of_sq_le
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowWMinorant v (t ^ 2) 1 := by
  have hz : (20 / 17 : ℝ) * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have h := lrLowWMinorant_one_nonneg hv hz
  have hscale : (17 / 20 : ℝ) * ((20 / 17 : ℝ) * t ^ 2) = t ^ 2 := by
    ring
  rw [hscale] at h
  exact h

theorem lrLowSecondScalar_one_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) 1 *
          lrLowR v (t ^ 2) (lrGShape t v) 1 +
        2 * (1 : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) 1 := by
  have hminorant := lrLowWMinorant_one_nonneg_of_sq_le
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) htSq
  have hbridge := lrLowWMinorant_le_second_scalar hv ht
    (n := 1) (by norm_num)
  norm_num at hbridge ⊢
  exact hminorant.trans hbridge

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
lemma lrLowWPolynomial_two_eq_power (v z : ℝ) :
    lrLowWPolynomial v ((17 / 20 : ℝ) * z) 2 =
      lrLowW2PowerEval v z := by
  unfold lrLowWPolynomial
  unfold lrLowWGRadialNumerator lrLowWALowerRadialNumerator
    lrLowWAUpperScaledNumerator lrLowWBetaUpperNumerator
  unfold lrLowWBetaDivVNumerator lrLowWMinusLogNumerator
    lrLowWBetaNumerator lrLowWRadialBase lrLowWXiDenominator
  unfold lrLowH lrLowPhiPrefix lrLowBnUpper
    lrLowPnLower lrLowL12 lrLowT lrLowA lrLowW2PowerEval
  unfold lrLowW2VPowerEvalCol0 lrLowW2VPowerEvalCol1 lrLowW2VPowerEvalCol2 lrLowW2VPowerEvalCol3 lrLowW2VPowerEvalCol4 lrLowW2VPowerEvalCol5 lrLowW2VPowerEvalCol6 lrLowW2VPowerEvalCol7 lrLowW2VPowerEvalCol8 lrLowW2VPowerEvalCol9 lrLowW2VPowerEvalCol10 lrLowW2VPowerEvalCol11 lrLowW2VPowerEvalCol12 lrLowW2VPowerEvalCol13 lrLowW2VPowerEvalCol14 lrLowW2VPowerEvalCol15 lrLowW2VPowerEvalCol16 lrLowW2VPowerEvalCol17 lrLowW2VPowerEvalCol18 lrLowW2VPowerEvalCol19 lrLowW2VPowerEvalCol20 lrLowW2VPowerEvalCol21 lrLowW2VPowerEvalCol22 lrLowW2VPowerEvalCol23 lrLowW2VPowerEvalCol24 lrLowW2VPowerEvalCol25
  norm_num [Finset.sum_range_succ]
  ring

lemma lrLowWMinorant_nonneg_of_polynomial_certificate
    {v z P : ℝ} {n : ℕ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1)
    (hpoly : lrLowWPolynomial v ((17 / 20 : ℝ) * z) n = P)
    (hcertificate : 0 ≤ P) :
    0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) n := by
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hv.1.le (sub_nonneg.mpr hv.2)]
  have hvz : v ^ 2 * z ≤ 1 := by
    calc
      v ^ 2 * z ≤ 1 * 1 := mul_le_mul hvSq hz.2 hz.1 (by norm_num)
      _ = 1 := by norm_num
  have hxiPos : 0 < 1 - v ^ 2 * ((17 / 20 : ℝ) * z) := by
    nlinarith
  have hxi : 1 - v ^ 2 * ((17 / 20 : ℝ) * z) ≠ 0 := hxiPos.ne'
  have hproduct :
      0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) n *
        (lrLowWRadialBase v *
          lrLowWXiDenominator v ((17 / 20 : ℝ) * z)) := by
    rw [lrLowWMinorant_mul_base_eq_polynomial hv.1.ne' h1 h2 hxi,
      hpoly]
    exact hcertificate
  have hradial : 0 < lrLowWRadialBase v := by
    unfold lrLowWRadialBase
    exact mul_pos (pow_pos (by linarith [hv.1]) _)
      (pow_pos (by linarith [hv.1]) _)
  have hden : 0 < lrLowWXiDenominator v ((17 / 20 : ℝ) * z) := by
    unfold lrLowWXiDenominator
    nlinarith
  exact nonneg_of_mul_nonneg_left hproduct (mul_pos hradial hden)

theorem lrLowWMinorant_two_nonneg
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) 2 := by
  apply lrLowWMinorant_nonneg_of_polynomial_certificate hv hz
    (lrLowWPolynomial_two_eq_power v z)
  rw [← lrLowW2Bernstein_eq_power]
  exact lrLowW2Bernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz

theorem lrLowWMinorant_two_nonneg_of_sq_le
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowWMinorant v (t ^ 2) 2 := by
  have hz : (20 / 17 : ℝ) * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have h := lrLowWMinorant_two_nonneg hv hz
  have hscale : (17 / 20 : ℝ) * ((20 / 17 : ℝ) * t ^ 2) = t ^ 2 := by
    ring
  rw [hscale] at h
  exact h

theorem lrLowSecondScalar_two_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) 2 *
          lrLowR v (t ^ 2) (lrGShape t v) 2 +
        2 * (2 : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) 2 := by
  have hminorant := lrLowWMinorant_two_nonneg_of_sq_le
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) htSq
  have hbridge := lrLowWMinorant_le_second_scalar hv ht
    (n := 2) (by norm_num)
  norm_num at hbridge ⊢
  exact hminorant.trans hbridge

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
lemma lrLowWPolynomial_three_eq_power (v z : ℝ) :
    lrLowWPolynomial v ((17 / 20 : ℝ) * z) 3 =
      lrLowW3PowerEval v z := by
  unfold lrLowWPolynomial
  unfold lrLowWGRadialNumerator lrLowWALowerRadialNumerator
    lrLowWAUpperScaledNumerator lrLowWBetaUpperNumerator
  unfold lrLowWBetaDivVNumerator lrLowWMinusLogNumerator
    lrLowWBetaNumerator lrLowWRadialBase lrLowWXiDenominator
  unfold lrLowH lrLowPhiPrefix lrLowBnUpper
    lrLowPnLower lrLowL12 lrLowT lrLowA lrLowW3PowerEval
  unfold lrLowW3VPowerEvalCol0 lrLowW3VPowerEvalCol1 lrLowW3VPowerEvalCol2 lrLowW3VPowerEvalCol3 lrLowW3VPowerEvalCol4 lrLowW3VPowerEvalCol5 lrLowW3VPowerEvalCol6 lrLowW3VPowerEvalCol7 lrLowW3VPowerEvalCol8 lrLowW3VPowerEvalCol9 lrLowW3VPowerEvalCol10 lrLowW3VPowerEvalCol11 lrLowW3VPowerEvalCol12 lrLowW3VPowerEvalCol13 lrLowW3VPowerEvalCol14 lrLowW3VPowerEvalCol15 lrLowW3VPowerEvalCol16 lrLowW3VPowerEvalCol17 lrLowW3VPowerEvalCol18 lrLowW3VPowerEvalCol19 lrLowW3VPowerEvalCol20 lrLowW3VPowerEvalCol21 lrLowW3VPowerEvalCol22 lrLowW3VPowerEvalCol23 lrLowW3VPowerEvalCol24 lrLowW3VPowerEvalCol25
  norm_num [Finset.sum_range_succ]
  ring

theorem lrLowWMinorant_three_nonneg
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) 3 := by
  apply lrLowWMinorant_nonneg_of_polynomial_certificate hv hz
    (lrLowWPolynomial_three_eq_power v z)
  rw [← lrLowW3Bernstein_eq_power]
  exact lrLowW3Bernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz

theorem lrLowWMinorant_three_nonneg_of_sq_le
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowWMinorant v (t ^ 2) 3 := by
  have hz : (20 / 17 : ℝ) * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have h := lrLowWMinorant_three_nonneg hv hz
  have hscale : (17 / 20 : ℝ) * ((20 / 17 : ℝ) * t ^ 2) = t ^ 2 := by
    ring
  rw [hscale] at h
  exact h

theorem lrLowSecondScalar_three_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) 3 *
          lrLowR v (t ^ 2) (lrGShape t v) 3 +
        2 * (3 : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) 3 := by
  have hminorant := lrLowWMinorant_three_nonneg_of_sq_le
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) htSq
  have hbridge := lrLowWMinorant_le_second_scalar hv ht
    (n := 3) (by norm_num)
  norm_num at hbridge ⊢
  exact hminorant.trans hbridge

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
lemma lrLowWPolynomial_four_eq_power (v z : ℝ) :
    lrLowWPolynomial v ((17 / 20 : ℝ) * z) 4 =
      lrLowW4PowerEval v z := by
  unfold lrLowWPolynomial
  unfold lrLowWGRadialNumerator lrLowWALowerRadialNumerator
    lrLowWAUpperScaledNumerator lrLowWBetaUpperNumerator
  unfold lrLowWBetaDivVNumerator lrLowWMinusLogNumerator
    lrLowWBetaNumerator lrLowWRadialBase lrLowWXiDenominator
  unfold lrLowH lrLowPhiPrefix lrLowBnUpper
    lrLowPnLower lrLowL12 lrLowT lrLowA lrLowW4PowerEval
  unfold lrLowW4VPowerEvalCol0 lrLowW4VPowerEvalCol1 lrLowW4VPowerEvalCol2 lrLowW4VPowerEvalCol3 lrLowW4VPowerEvalCol4 lrLowW4VPowerEvalCol5 lrLowW4VPowerEvalCol6 lrLowW4VPowerEvalCol7 lrLowW4VPowerEvalCol8 lrLowW4VPowerEvalCol9 lrLowW4VPowerEvalCol10 lrLowW4VPowerEvalCol11 lrLowW4VPowerEvalCol12 lrLowW4VPowerEvalCol13 lrLowW4VPowerEvalCol14 lrLowW4VPowerEvalCol15 lrLowW4VPowerEvalCol16 lrLowW4VPowerEvalCol17 lrLowW4VPowerEvalCol18 lrLowW4VPowerEvalCol19 lrLowW4VPowerEvalCol20 lrLowW4VPowerEvalCol21 lrLowW4VPowerEvalCol22 lrLowW4VPowerEvalCol23 lrLowW4VPowerEvalCol24 lrLowW4VPowerEvalCol25
  norm_num [Finset.sum_range_succ]
  ring

theorem lrLowWMinorant_four_nonneg
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) 4 := by
  apply lrLowWMinorant_nonneg_of_polynomial_certificate hv hz
    (lrLowWPolynomial_four_eq_power v z)
  rw [← lrLowW4Bernstein_eq_power]
  exact lrLowW4Bernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz

theorem lrLowWMinorant_four_nonneg_of_sq_le
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowWMinorant v (t ^ 2) 4 := by
  have hz : (20 / 17 : ℝ) * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have h := lrLowWMinorant_four_nonneg hv hz
  have hscale : (17 / 20 : ℝ) * ((20 / 17 : ℝ) * t ^ 2) = t ^ 2 := by
    ring
  rw [hscale] at h
  exact h

theorem lrLowSecondScalar_four_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) 4 *
          lrLowR v (t ^ 2) (lrGShape t v) 4 +
        2 * (4 : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) 4 := by
  have hminorant := lrLowWMinorant_four_nonneg_of_sq_le
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) htSq
  have hbridge := lrLowWMinorant_le_second_scalar hv ht
    (n := 4) (by norm_num)
  norm_num at hbridge ⊢
  exact hminorant.trans hbridge

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
lemma lrLowWPolynomial_five_eq_power (v z : ℝ) :
    lrLowWPolynomial v ((17 / 20 : ℝ) * z) 5 =
      lrLowW5PowerEval v z := by
  unfold lrLowWPolynomial
  unfold lrLowWGRadialNumerator lrLowWALowerRadialNumerator
    lrLowWAUpperScaledNumerator lrLowWBetaUpperNumerator
  unfold lrLowWBetaDivVNumerator lrLowWMinusLogNumerator
    lrLowWBetaNumerator lrLowWRadialBase lrLowWXiDenominator
  unfold lrLowH lrLowPhiPrefix lrLowBnUpper
    lrLowPnLower lrLowL12 lrLowT lrLowA lrLowW5PowerEval
  unfold lrLowW5VPowerEvalCol0 lrLowW5VPowerEvalCol1 lrLowW5VPowerEvalCol2 lrLowW5VPowerEvalCol3 lrLowW5VPowerEvalCol4 lrLowW5VPowerEvalCol5 lrLowW5VPowerEvalCol6 lrLowW5VPowerEvalCol7 lrLowW5VPowerEvalCol8 lrLowW5VPowerEvalCol9 lrLowW5VPowerEvalCol10 lrLowW5VPowerEvalCol11 lrLowW5VPowerEvalCol12 lrLowW5VPowerEvalCol13 lrLowW5VPowerEvalCol14 lrLowW5VPowerEvalCol15 lrLowW5VPowerEvalCol16 lrLowW5VPowerEvalCol17 lrLowW5VPowerEvalCol18 lrLowW5VPowerEvalCol19 lrLowW5VPowerEvalCol20 lrLowW5VPowerEvalCol21 lrLowW5VPowerEvalCol22 lrLowW5VPowerEvalCol23 lrLowW5VPowerEvalCol24 lrLowW5VPowerEvalCol25
  norm_num [Finset.sum_range_succ]
  ring

theorem lrLowWMinorant_five_nonneg
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowWMinorant v ((17 / 20 : ℝ) * z) 5 := by
  apply lrLowWMinorant_nonneg_of_polynomial_certificate hv hz
    (lrLowWPolynomial_five_eq_power v z)
  rw [← lrLowW5Bernstein_eq_power]
  exact lrLowW5Bernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz

theorem lrLowWMinorant_five_nonneg_of_sq_le
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowWMinorant v (t ^ 2) 5 := by
  have hz : (20 / 17 : ℝ) * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have h := lrLowWMinorant_five_nonneg hv hz
  have hscale : (17 / 20 : ℝ) * ((20 / 17 : ℝ) * t ^ 2) = t ^ 2 := by
    ring
  rw [hscale] at h
  exact h

theorem lrLowSecondScalar_five_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) 5 *
          lrLowR v (t ^ 2) (lrGShape t v) 5 +
        2 * (5 : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) 5 := by
  have hminorant := lrLowWMinorant_five_nonneg_of_sq_le
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) htSq
  have hbridge := lrLowWMinorant_le_second_scalar hv ht
    (n := 5) (by norm_num)
  norm_num at hbridge ⊢
  exact hminorant.trans hbridge

end CourtadeKumar
