import InformationTheory.CourtadeKumar.LRLowShapeVStarPower

/-!
# Exact rectangle certificate for the low-shape `V_*` envelope

This directly certifies a rational lower envelope on the full
`x ≤ 17/20` rectangle.  It is stronger than checking only the outer endpoint
and avoids introducing an additional analytic monotonicity layer.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowVStarEnvelopeLower (v x : ℝ) : ℝ :=
  lrLowGShapeLower v x -
    2 * (1 - v ^ 2 * x) *
      (lrLowVBetaEndpointUpper v + lrLowL12Upper (v ^ 2 * x)) /
      (v * (1 + v))

noncomputable def lrLowVStarCertificateBase (v z : ℝ) : ℝ :=
  (1 + v) ^ 9 * (2 + v) ^ 9 *
    (20 - 17 * z) * (20 - 17 * v ^ 2 * z)

noncomputable def lrLowVStarEnvelopePolynomial (v z : ℝ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  let q := v ^ 2 * x
  lrLowVGPolynomial v z -
    2 * ((1 - q) * (lrLowVBetaEndpointUpper v + lrLowL12 q) + q ^ 13 / 26) *
      lrLowVStarCertificateBase v z / (v * (1 + v))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma lrLowVStarEnvelope_scaled_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVStarEnvelopeLower v ((17 / 20 : ℝ) * z) *
        lrLowVStarCertificateBase v z =
      lrLowVStarEnvelopePolynomial v z := by
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
      (by linarith [hv.1] : 0 ≤ 1 + v)]
  have hq : 1 - v ^ 2 * ((17 / 20 : ℝ) * z) ≠ 0 := by
    have hz0 : 0 ≤ (17 / 20 : ℝ) * z := mul_nonneg (by norm_num) hz.1
    have hle : v ^ 2 * ((17 / 20 : ℝ) * z) ≤ 17 / 20 := calc
      v ^ 2 * ((17 / 20 : ℝ) * z) ≤ 1 * ((17 / 20 : ℝ) * z) :=
        mul_le_mul_of_nonneg_right hvSq hz0
      _ ≤ 17 / 20 := by
        convert mul_le_mul_of_nonneg_left hz.2
          (by norm_num : (0 : ℝ) ≤ 17 / 20) using 1 <;> ring
    norm_num at hle ⊢
    linarith
  set q : ℝ := v ^ 2 * ((17 / 20 : ℝ) * z) with hqDef
  have hq' : 1 - q ≠ 0 := by simpa only [hqDef] using hq
  have htailQ :
      (1 - q) * (lrLowVBetaEndpointUpper v + lrLowL12Upper q) =
        (1 - q) * (lrLowVBetaEndpointUpper v + lrLowL12 q) + q ^ 13 / 26 := by
    unfold lrLowL12Upper
    field_simp [hq']
    ring
  have htail :
      (1 - v ^ 2 * ((17 / 20 : ℝ) * z)) *
          (lrLowVBetaEndpointUpper v +
            lrLowL12Upper (v ^ 2 * ((17 / 20 : ℝ) * z))) =
        (1 - v ^ 2 * ((17 / 20 : ℝ) * z)) *
          (lrLowVBetaEndpointUpper v +
            lrLowL12 (v ^ 2 * ((17 / 20 : ℝ) * z))) +
          (v ^ 2 * ((17 / 20 : ℝ) * z)) ^ 13 / 26 := by
    simpa only [hqDef] using htailQ
  have hextra :
      2 * (1 - v ^ 2 * ((17 / 20 : ℝ) * z)) *
            (lrLowVBetaEndpointUpper v +
              lrLowL12Upper (v ^ 2 * ((17 / 20 : ℝ) * z))) /
            (v * (1 + v)) * lrLowVStarCertificateBase v z =
        2 * ((1 - v ^ 2 * ((17 / 20 : ℝ) * z)) *
              (lrLowVBetaEndpointUpper v +
                lrLowL12 (v ^ 2 * ((17 / 20 : ℝ) * z))) +
              (v ^ 2 * ((17 / 20 : ℝ) * z)) ^ 13 / 26) *
            lrLowVStarCertificateBase v z / (v * (1 + v)) := by
    rw [show
      2 * (1 - v ^ 2 * ((17 / 20 : ℝ) * z)) *
          (lrLowVBetaEndpointUpper v +
            lrLowL12Upper (v ^ 2 * ((17 / 20 : ℝ) * z))) =
        2 * ((1 - v ^ 2 * ((17 / 20 : ℝ) * z)) *
          (lrLowVBetaEndpointUpper v +
            lrLowL12Upper (v ^ 2 * ((17 / 20 : ℝ) * z)))) by ring,
      htail]
    ring
  have hg := lrLowVG_scaled_eq_polynomial hv hz
  change lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
      lrLowVStarCertificateBase v z = lrLowVGPolynomial v z at hg
  unfold lrLowVStarEnvelopeLower lrLowVStarEnvelopePolynomial
  dsimp only
  rw [sub_mul, hg, hextra]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma lrLowVStarEnvelope_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVStarEnvelopePolynomial v z * 6450271027200000000000000 =
      lrLowVEPowerEval v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  unfold lrLowVStarEnvelopePolynomial lrLowVGPolynomial
    lrLowPhiFirst12 lrLowPhiSecond12 lrLowVBetaEndpointUpper
    lrLowL12 lrLowGLower lrLowBetaLower lrLowMinusLogLower
    lrAtanh5 lrLowVStarCertificateBase lrLowVEPowerEval
  unfold lrLowVEVPowerEvalCol0 lrLowVEVPowerEvalCol1
    lrLowVEVPowerEvalCol2 lrLowVEVPowerEvalCol3
    lrLowVEVPowerEvalCol4 lrLowVEVPowerEvalCol5
    lrLowVEVPowerEvalCol6 lrLowVEVPowerEvalCol7
    lrLowVEVPowerEvalCol8 lrLowVEVPowerEvalCol9
    lrLowVEVPowerEvalCol10 lrLowVEVPowerEvalCol11
    lrLowVEVPowerEvalCol12 lrLowVEVPowerEvalCol13
    lrLowVEVPowerEvalCol14 lrLowVEVPowerEvalCol15 lrLowA
  norm_num [Finset.sum_range_succ, Nat.choose]
  field_simp [hv0, h1, h2]
  ring

lemma lrLowVStarEnvelope_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVStarEnvelopeLower v ((17 / 20 : ℝ) * z) *
        lrLowVStarCertificateBase v z * 6450271027200000000000000 =
      lrLowVEPowerEval v z := by
  rw [lrLowVStarEnvelope_scaled_eq_polynomial hv hz]
  exact lrLowVStarEnvelope_polynomial_eq_power hv

theorem lrLowVStarEnvelopeLower_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVStarEnvelopeLower v ((17 / 20 : ℝ) * z) := by
  have hbern := lrLowVEBernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hpower : 0 ≤ lrLowVEPowerEval v z := by
    rw [← lrLowVEBernstein_eq_power]
    exact hbern
  have hid := lrLowVStarEnvelope_certificate_identity hv hz
  have hbase : 0 < lrLowVStarCertificateBase v z := by
    unfold lrLowVStarCertificateBase
    have hvSq : v ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
        (by linarith [hv.1] : 0 ≤ 1 + v)]
    have hzv : v ^ 2 * z ≤ 1 := calc
      v ^ 2 * z ≤ 1 * z := mul_le_mul_of_nonneg_right hvSq hz.1
      _ ≤ 1 := by simpa using hz.2
    exact mul_pos
      (mul_pos (mul_pos (pow_pos (by linarith [hv.1]) _)
        (pow_pos (by linarith [hv.1]) _)) (by nlinarith [hz.2]))
      (by nlinarith)
  have hscale : 0 < lrLowVStarCertificateBase v z *
      (6450271027200000000000000 : ℝ) := mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowVStarCertificateBase v z * 6450271027200000000000000) *
        lrLowVStarEnvelopeLower v ((17 / 20 : ℝ) * z) := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVStarEnvelopeLower_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVStarEnvelopeLower v x := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVStarEnvelopeLower_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
