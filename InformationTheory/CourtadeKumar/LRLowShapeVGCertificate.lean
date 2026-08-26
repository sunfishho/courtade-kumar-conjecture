import InformationTheory.CourtadeKumar.LRLowShapeVGPower

/-! Semantic wrapper for the generated low-shape `G` certificate. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowVGCertificateBase (v z : ℝ) : ℝ :=
  (1 + v) ^ 9 * (2 + v) ^ 9 *
    (20 - 17 * z) * (20 - 17 * v ^ 2 * z)

noncomputable def lrLowVGPolynomial (v z : ℝ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  let radial := (1 + v) ^ 9 * (2 + v) ^ 9
  let dx := 20 - 17 * z
  let dxi := 20 - 17 * v ^ 2 * z
  (lrLowGLower v - lrLowPhiFirst12 x - lrLowPhiSecond12 v x) *
      radial * dx * dxi -
    20 * lrLowA 13 * x ^ 13 * radial * dxi -
    20 * lrLowA 13 * x ^ 13 * v ^ 25 * radial * dx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma lrLowVG_scaled_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
        lrLowVGCertificateBase v z =
      lrLowVGPolynomial v z := by
  have hx : 1 - (17 / 20 : ℝ) * z ≠ 0 := by
    have : (17 / 20 : ℝ) * z ≤ (17 / 20 : ℝ) := by
      convert mul_le_mul_of_nonneg_left hz.2
        (by norm_num : (0 : ℝ) ≤ 17 / 20) using 1 <;> ring
    norm_num at this ⊢
    linarith
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
      (by linarith [hv.1] : 0 ≤ 1 + v)]
  have hq : 1 - v ^ 2 * ((17 / 20 : ℝ) * z) ≠ 0 := by
    have hz0 : 0 ≤ (17 / 20 : ℝ) * z := mul_nonneg (by norm_num) hz.1
    have hle : v ^ 2 * ((17 / 20 : ℝ) * z) ≤ 17 / 20 := calc
      v ^ 2 * ((17 / 20 : ℝ) * z) ≤ 1 * ((17 / 20 : ℝ) * z) :=
        mul_le_mul_of_nonneg_right hvSq hz0
      _ ≤ 17 / 20 := by
        simpa using mul_le_mul_of_nonneg_left hz.2
          (by norm_num : (0 : ℝ) ≤ 17 / 20)
    norm_num at hle ⊢
    linarith
  unfold lrLowGShapeLower lrLowPhi12Upper lrLowVGCertificateBase
    lrLowVGPolynomial
  dsimp only
  have hdxScale : 20 - 17 * z =
      20 * (1 - (17 / 20 : ℝ) * z) := by ring
  have hdqScale : 20 - 17 * v ^ 2 * z =
      20 * (1 - v ^ 2 * ((17 / 20 : ℝ) * z)) := by ring
  rw [hdxScale, hdqScale]
  set dx : ℝ := 1 - (17 / 20 : ℝ) * z with hdxDef
  set dxi : ℝ := 1 - v ^ 2 * ((17 / 20 : ℝ) * z) with hdxiDef
  have hdx0 : dx ≠ 0 := by simpa only [hdxDef] using hx
  have hdxi0 : dxi ≠ 0 := by simpa only [hdxiDef] using hq
  field_simp [hdx0, hdxi0]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma lrLowVG_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVGPolynomial v z * 3225135513600000000000000 =
      lrLowVGPowerEval v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  unfold lrLowVGPolynomial lrLowPhiFirst12
    lrLowPhiSecond12 lrLowGLower lrLowBetaLower lrLowMinusLogLower
    lrAtanh5 lrLowVGPowerEval
  unfold lrLowVGVPowerEvalCol0 lrLowVGVPowerEvalCol1
    lrLowVGVPowerEvalCol2 lrLowVGVPowerEvalCol3
    lrLowVGVPowerEvalCol4 lrLowVGVPowerEvalCol5
    lrLowVGVPowerEvalCol6 lrLowVGVPowerEvalCol7
    lrLowVGVPowerEvalCol8 lrLowVGVPowerEvalCol9
    lrLowVGVPowerEvalCol10 lrLowVGVPowerEvalCol11
    lrLowVGVPowerEvalCol12 lrLowVGVPowerEvalCol13
    lrLowVGVPowerEvalCol14 lrLowA
  norm_num [Finset.sum_range_succ, Nat.choose]
  field_simp [hv0, h1, h2]
  ring

lemma lrLowVG_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
        lrLowVGCertificateBase v z * 3225135513600000000000000 =
      lrLowVGPowerEval v z := by
  rw [lrLowVG_scaled_eq_polynomial hv hz]
  exact lrLowVG_polynomial_eq_power hv

theorem lrLowGShapeLower_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowGShapeLower v ((17 / 20 : ℝ) * z) := by
  have hbern := lrLowVGLowerBernstein_nonneg
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hpower : 0 ≤ lrLowVGPowerEval v z := by
    rw [← lrLowVGBernstein_eq_power]
    exact hbern
  have hid := lrLowVG_certificate_identity hv hz
  have hbase : 0 < lrLowVGCertificateBase v z := by
    unfold lrLowVGCertificateBase
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
  have hprod : 0 ≤
      lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
        lrLowVGCertificateBase v z * 3225135513600000000000000 := by
    rw [hid]
    exact hpower
  have hscale : 0 < lrLowVGCertificateBase v z *
      (3225135513600000000000000 : ℝ) := mul_pos hbase (by norm_num)
  have hprod' : 0 ≤
      lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
        (lrLowVGCertificateBase v z * 3225135513600000000000000) := by
    simpa only [mul_assoc] using hprod
  have hprod'' : 0 ≤
      (lrLowVGCertificateBase v z * 3225135513600000000000000) *
        lrLowGShapeLower v ((17 / 20 : ℝ) * z) := by
    simpa only [mul_comm] using hprod'
  exact nonneg_of_mul_nonneg_right hprod'' hscale

theorem lrLowGShapeLower_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowGShapeLower v x := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowGShapeLower_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
