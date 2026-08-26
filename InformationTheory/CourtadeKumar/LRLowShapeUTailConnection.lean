import InformationTheory.CourtadeKumar.LRLowShapeUTailSemanticPower

/-! Connection of the exact uniform U-tail certificate to every actual
second scalar with index `n ≥ 6`. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowPhiFirstUpper (x : ℝ) : ℝ :=
  lrLowPhiFirst12 x + lrLowA 13 * x ^ 13 / (1 - x)

noncomputable def lrLowJLower (x : ℝ) : ℝ :=
  (693147 : ℝ) / 1000000 - lrLowPhiFirstUpper x

noncomputable def lrLowGeometricSix (xi : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, xi ^ j

noncomputable def lrLowUTailMinorant (v x : ℝ) : ℝ :=
  2 * lrLowJLower x + (1 - v) / v * lrLowALower v x -
    lrLowTailH v * lrLowBnUpper 6 -
    lrLowAUpper v x / (v * (1 + v) * lrLowGeometricSix (v ^ 2 * x))

noncomputable def lrLowUTailBase (v z : ℝ) : ℝ :=
  (1 + v) ^ 2 * (2 + v) ^ 9 * (20 - 17 * z) *
    (20 - 17 * v ^ 2 * z) * lrLowUTailGeometricNumerator v z

lemma lrLowL12_eq_v_mul_divNumerator (v x : ℝ) :
    lrLowL12 (v ^ 2 * x) = v * lrLowWLDivVNumerator v x := by
  unfold lrLowL12 lrLowWLDivVNumerator
  norm_num [Finset.sum_range_succ]
  ring_nf

lemma lrLowUTailGeometricNumerator_eq (v z : ℝ) :
    lrLowUTailGeometricNumerator v z =
      20 ^ 5 * lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)) := by
  unfold lrLowUTailGeometricNumerator lrLowGeometricSix
  norm_num [Finset.sum_range_succ]
  ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
lemma lrLowUTailMinorant_mul_base_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowUTailMinorant v ((17 / 20 : ℝ) * z) * lrLowUTailBase v z =
      lrLowUTailPolynomial v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have hx : (17 / 20 : ℝ) * z < 1 := by nlinarith [hz.2]
  have hxden : 1 - (17 / 20 : ℝ) * z ≠ 0 := by nlinarith
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hv.1.le (sub_nonneg.mpr hv.2)]
  have hvz : v ^ 2 * z ≤ 1 := by
    calc
      v ^ 2 * z ≤ 1 * 1 := mul_le_mul hvSq hz.2 hz.1 (by norm_num)
      _ = 1 := by norm_num
  have hxiden : 1 - v ^ 2 * ((17 / 20 : ℝ) * z) ≠ 0 := by
    nlinarith
  have hdx : 20 - 17 * z ≠ 0 := by nlinarith [hz.2]
  have hdxi : 20 - 17 * v ^ 2 * z ≠ 0 := by nlinarith [hvz]
  have hdxi' : 20 - v ^ 2 * z * 17 ≠ 0 := by nlinarith [hvz]
  have hdxi'' : 20 - z * v ^ 2 * 17 ≠ 0 := by nlinarith [hvz]
  have hgeomPos : 0 < lrLowGeometricSix
      (v ^ 2 * ((17 / 20 : ℝ) * z)) := by
    have hxi : 0 ≤ v ^ 2 * ((17 / 20 : ℝ) * z) := by
      exact mul_nonneg (sq_nonneg v) (mul_nonneg (by norm_num) hz.1)
    unfold lrLowGeometricSix
    norm_num [Finset.sum_range_succ]
    positivity
  have hgeom : lrLowGeometricSix
      (v ^ 2 * ((17 / 20 : ℝ) * z)) ≠ 0 := hgeomPos.ne'
  have hgeom' : lrLowGeometricSix
      (z * v ^ 2 * (17 / 20 : ℝ)) ≠ 0 := by
    convert hgeom using 1 <;> ring
  have hgeom'' : lrLowGeometricSix
      (v ^ 2 * z * (17 / 20 : ℝ)) ≠ 0 := by
    convert hgeom using 1 <;> ring
  have hgeomNorm : lrLowGeometricSix
      (v ^ 2 * 17 * z / 20) ≠ 0 := by
    convert hgeom using 1 <;> ring
  have hbeta : lrLowBetaLower v =
      v * lrLowWBetaDivVNumerator v / (2 + v) ^ 9 := by
    have hb := lrLowBetaLower_mul_denominator h2
    have hnum : lrLowWBetaNumerator v =
        v * lrLowWBetaDivVNumerator v := by
      unfold lrLowWBetaNumerator lrLowWBetaDivVNumerator
      ring
    rw [hnum] at hb
    exact (eq_div_iff (pow_ne_zero 9 h2)).2 hb
  have hbetaUpper : lrAtanh5Upper (v / (2 + v)) =
      v * lrLowWBetaUpperDivVNumerator v /
        ((1 + v) * (2 + v) ^ 9) := by
    have hb := lrAtanh5Upper_mul_denominator h1 h2
    have hnum : lrLowWBetaUpperNumerator v =
        v * lrLowWBetaUpperDivVNumerator v := by
      unfold lrLowWBetaUpperNumerator lrLowWBetaUpperDivVNumerator
        lrLowWBetaNumerator lrLowWBetaDivVNumerator
      ring
    rw [hnum] at hb
    have hb' : lrAtanh5Upper (v / (2 + v)) *
        ((1 + v) * (2 + v) ^ 9) =
          v * lrLowWBetaUpperDivVNumerator v := by
      simpa [mul_assoc] using hb
    exact (eq_div_iff (mul_ne_zero h1 (pow_ne_zero 9 h2))).2 hb'
  have hj :
      2 * lrLowJLower ((17 / 20 : ℝ) * z) * lrLowUTailBase v z =
        lrLowUTailJHeadPolynomial v z + lrLowUTailJTailPolynomial v z := by
    unfold lrLowJLower lrLowPhiFirstUpper lrLowPhiFirst12 lrLowUTailBase
      lrLowUTailJHeadPolynomial lrLowUTailJTailPolynomial
    norm_num [Finset.sum_range_succ]
    field_simp [hxden, hdx]
    ring
  have ha :
      (1 - v) / v * lrLowALower v ((17 / 20 : ℝ) * z) *
          lrLowUTailBase v z = lrLowUTailALowerPolynomial v z := by
    unfold lrLowALower lrLowUTailBase lrLowUTailALowerPolynomial
    rw [hbeta, lrLowL12_eq_v_mul_divNumerator]
    field_simp [hv0, h2]
  have hh :
      -(lrLowTailH v * lrLowBnUpper 6) * lrLowUTailBase v z =
        lrLowUTailHPolynomial v z := by
    unfold lrLowTailH lrFlowM lrLowUTailBase lrLowUTailHPolynomial
    field_simp [h1]
  have huBeta :
      -(lrAtanh5Upper (v / (2 + v)) /
          (v * (1 + v) *
            lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
          lrLowUTailBase v z =
        -(20 : ℝ) ^ 5 *
          (lrLowWBetaUpperDivVNumerator v * (20 - 17 * z) *
            (20 - 17 * v ^ 2 * z)) := by
    unfold lrLowUTailBase
    rw [hbetaUpper, lrLowUTailGeometricNumerator_eq]
    field_simp [hv0, h1, h2, hgeom]
  have huL :
      -(lrLowL12 (v ^ 2 * ((17 / 20 : ℝ) * z)) /
          (v * (1 + v) *
            lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
          lrLowUTailBase v z =
        -(20 : ℝ) ^ 5 *
          ((1 + v) * (2 + v) ^ 9 * (20 - 17 * z) *
            (20 - 17 * v ^ 2 * z) *
            lrLowWLDivVNumerator v ((17 / 20 : ℝ) * z)) := by
    unfold lrLowUTailBase
    rw [lrLowL12_eq_v_mul_divNumerator,
      lrLowUTailGeometricNumerator_eq]
    field_simp [hv0, h1, hgeom]
  have huTail :
      -((v ^ 2 * ((17 / 20 : ℝ) * z)) ^ 13 /
          (26 * (1 - v ^ 2 * ((17 / 20 : ℝ) * z))) /
          (v * (1 + v) *
            lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
          lrLowUTailBase v z =
        -(20 : ℝ) ^ 5 *
          ((20 / 26 : ℝ) * (1 + v) * (2 + v) ^ 9 *
            (20 - 17 * z) * v ^ 25 *
            ((17 / 20 : ℝ) * z) ^ 13) := by
    have hcombined :
        -(z * v ^ 2 * lrLowGeometricSix (z * v ^ 2 * (17 / 20 : ℝ)) * 17) +
            lrLowGeometricSix (z * v ^ 2 * (17 / 20 : ℝ)) * 20 ≠ 0 := by
      rw [show
        -(z * v ^ 2 * lrLowGeometricSix (z * v ^ 2 * (17 / 20 : ℝ)) * 17) +
            lrLowGeometricSix (z * v ^ 2 * (17 / 20 : ℝ)) * 20 =
          lrLowGeometricSix (z * v ^ 2 * (17 / 20 : ℝ)) *
            (20 - v ^ 2 * z * 17) by ring]
      exact mul_ne_zero hgeom' hdxi'
    unfold lrLowUTailBase
    rw [lrLowUTailGeometricNumerator_eq]
    field_simp [hv0, h1, hxiden, hgeom]
    ring_nf
    field_simp [hcombined]
    ring_nf
  have hu :
      -(lrLowAUpper v ((17 / 20 : ℝ) * z) /
          (v * (1 + v) *
            lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
          lrLowUTailBase v z = lrLowUTailAUpperPolynomial v z := by
    unfold lrLowAUpper lrLowL12Upper lrLowUTailAUpperPolynomial
    calc
      -((lrAtanh5Upper (v / (2 + v)) +
            (lrLowL12 (v ^ 2 * ((17 / 20 : ℝ) * z)) +
              (v ^ 2 * ((17 / 20 : ℝ) * z)) ^ 13 /
                (26 * (1 - v ^ 2 * ((17 / 20 : ℝ) * z))))) /
          (v * (1 + v) *
            lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
          lrLowUTailBase v z =
        -(lrAtanh5Upper (v / (2 + v)) /
            (v * (1 + v) *
              lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
            lrLowUTailBase v z +
          -(lrLowL12 (v ^ 2 * ((17 / 20 : ℝ) * z)) /
            (v * (1 + v) *
              lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
            lrLowUTailBase v z +
          -((v ^ 2 * ((17 / 20 : ℝ) * z)) ^ 13 /
            (26 * (1 - v ^ 2 * ((17 / 20 : ℝ) * z))) /
            (v * (1 + v) *
              lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
            lrLowUTailBase v z := by ring
      _ = -(20 : ℝ) ^ 5 *
          (lrLowWBetaUpperDivVNumerator v * (20 - 17 * z) *
              (20 - 17 * v ^ 2 * z) +
            (1 + v) * (2 + v) ^ 9 * (20 - 17 * z) *
              (20 - 17 * v ^ 2 * z) *
              lrLowWLDivVNumerator v ((17 / 20 : ℝ) * z) +
            (20 / 26 : ℝ) * (1 + v) * (2 + v) ^ 9 *
              (20 - 17 * z) * v ^ 25 *
              ((17 / 20 : ℝ) * z) ^ 13) := by
        rw [huBeta, huL, huTail]
        ring
  unfold lrLowUTailMinorant lrLowUTailPolynomial
  calc
    (2 * lrLowJLower ((17 / 20 : ℝ) * z) +
          (1 - v) / v * lrLowALower v ((17 / 20 : ℝ) * z) -
          lrLowTailH v * lrLowBnUpper 6 -
          lrLowAUpper v ((17 / 20 : ℝ) * z) /
            (v * (1 + v) *
              lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
        lrLowUTailBase v z =
      2 * lrLowJLower ((17 / 20 : ℝ) * z) * lrLowUTailBase v z +
        (1 - v) / v * lrLowALower v ((17 / 20 : ℝ) * z) *
          lrLowUTailBase v z +
        (-(lrLowTailH v * lrLowBnUpper 6)) * lrLowUTailBase v z +
        (-(lrLowAUpper v ((17 / 20 : ℝ) * z) /
          (v * (1 + v) *
            lrLowGeometricSix (v ^ 2 * ((17 / 20 : ℝ) * z)))) *
          lrLowUTailBase v z) := by ring
    _ = lrLowUTailJHeadPolynomial v z + lrLowUTailJTailPolynomial v z +
          lrLowUTailALowerPolynomial v z + lrLowUTailHPolynomial v z +
          lrLowUTailAUpperPolynomial v z := by rw [hj, ha, hh, hu]

theorem lrLowUTailMinorant_nonneg
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowUTailMinorant v ((17 / 20 : ℝ) * z) := by
  have hcert : 0 ≤ lrLowUTailPowerEval v z := by
    rw [← lrLowUTailBernstein_eq_power]
    exact lrLowUTailBernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hprod : 0 ≤ lrLowUTailMinorant v ((17 / 20 : ℝ) * z) *
      lrLowUTailBase v z := by
    rw [lrLowUTailMinorant_mul_base_eq_polynomial hv hz,
      lrLowUTailPolynomial_eq_power]
    exact hcert
  have hbase : 0 < lrLowUTailBase v z := by
    have hvp1 : 0 < 1 + v := by linarith [hv.1]
    have hvp2 : 0 < 2 + v := by linarith [hv.1]
    have hvSq : v ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hv.1.le (sub_nonneg.mpr hv.2)]
    have hvz : v ^ 2 * z ≤ 1 := by
      calc
        v ^ 2 * z ≤ 1 * 1 := mul_le_mul hvSq hz.2 hz.1 (by norm_num)
        _ = 1 := by norm_num
    have hdx : 0 < 20 - 17 * z := by nlinarith [hz.2]
    have hdxi : 0 < 20 - 17 * v ^ 2 * z := by nlinarith [hvz]
    have hxi : 0 ≤ v ^ 2 * ((17 / 20 : ℝ) * z) := by
      exact mul_nonneg (sq_nonneg v) (mul_nonneg (by norm_num) hz.1)
    have hgeomSix : 0 < lrLowGeometricSix
        (v ^ 2 * ((17 / 20 : ℝ) * z)) := by
      unfold lrLowGeometricSix
      norm_num [Finset.sum_range_succ]
      positivity
    have hgeom : 0 < lrLowUTailGeometricNumerator v z := by
      rw [lrLowUTailGeometricNumerator_eq]
      exact mul_pos (by norm_num) hgeomSix
    unfold lrLowUTailBase
    exact mul_pos
      (mul_pos (mul_pos (mul_pos (pow_pos hvp1 _) (pow_pos hvp2 _)) hdx) hdxi)
      hgeom
  exact nonneg_of_mul_nonneg_left hprod hbase

end CourtadeKumar
