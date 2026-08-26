import InformationTheory.CourtadeKumar.LRLowShapeVL7Power
import InformationTheory.CourtadeKumar.LRLowShapeUWPolynomialBridge
import InformationTheory.CourtadeKumar.LRLowShapeVGCertificate

/-! Semantic wrapper for the exact low-shape `L_7` certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowVL7CertificateBase (v z : ℝ) : ℝ :=
  (1 + v) ^ 9 * (2 + v) ^ 9 *
    (20 - 17 * z) * (20 - 17 * v ^ 2 * z)

noncomputable def lrLowVL7ConstantScaledPolynomial (v z : ℝ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  let q := v ^ 2 * x
  let dx := 20 - 17 * z
  let dxi := 20 - 17 * v ^ 2 * z
  (lrLowL12 q * dxi + 20 * q ^ 13 / 26) *
      (1 + v) ^ 8 * (2 + v) ^ 9 * dx +
    lrLowWBetaUpperNumerator v * v * x * (1 + v) ^ 7 * dx * dxi

noncomputable def lrLowVL7DeltaScaledPolynomial (v z : ℝ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  let q := v ^ 2 * x
  let dx := 20 - 17 * z
  let dxi := 20 - 17 * v ^ 2 * z
  (1 - v * x) / 2 *
    (∑ k ∈ Finset.range 6,
      ((7 - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
        q ^ (k + 1) * lrLowCStarLower (7 - (k + 1))) *
    (1 + v) ^ 8 * (2 + v) ^ 9 * dx * dxi

noncomputable def lrLowVL7Polynomial (v z : ℝ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  lrLowVGPolynomial v z * lrLowEHead (v ^ 2 * x) 7 -
    7 * lrLowVL7ConstantScaledPolynomial v z * lrLowCStarUpper 7 +
    lrLowVL7DeltaScaledPolynomial v z

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVL7Constant_mul_base_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVConstantUpper v ((17 / 20 : ℝ) * z) *
        lrLowVL7CertificateBase v z =
      lrLowVL7ConstantScaledPolynomial v z := by
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
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
  let q : ℝ := v ^ 2 * ((17 / 20 : ℝ) * z)
  have hq' : 1 - q ≠ 0 := by simpa only [q] using hq
  have hdq : 20 - 17 * v ^ 2 * z = 20 * (1 - q) := by
    dsimp only [q]
    ring
  have htail :
      lrLowL12Upper q * (20 - 17 * v ^ 2 * z) =
        lrLowL12 q * (20 - 17 * v ^ 2 * z) + 20 * q ^ 13 / 26 := by
    rw [hdq]
    unfold lrLowL12Upper
    field_simp [hq']
  have hupper := lrAtanh5Upper_mul_denominator h1 h2
  have hupper' : lrAtanh5Upper (v / (2 + v)) =
      lrLowWBetaUpperNumerator v / ((1 + v) * (2 + v) ^ 9) :=
    (eq_div_iff (mul_ne_zero h1 (pow_ne_zero 9 h2))).2 (by
      simpa only [mul_assoc] using hupper)
  unfold lrLowVConstantUpper lrLowVL7CertificateBase
    lrLowVL7ConstantScaledPolynomial lrFlowM
  dsimp only
  change
    (lrLowL12Upper q / (1 + v) +
        lrAtanh5Upper (v / (2 + v)) * (v / (1 + v)) *
          ((17 / 20 : ℝ) * z)) *
      ((1 + v) ^ 9 * (2 + v) ^ 9 * (20 - 17 * z) *
        (20 - 17 * v ^ 2 * z)) = _
  rw [hupper']
  calc
    _ = (lrLowL12Upper q * (20 - 17 * v ^ 2 * z)) *
          (1 + v) ^ 8 * (2 + v) ^ 9 * (20 - 17 * z) +
        lrLowWBetaUpperNumerator v * v * ((17 / 20 : ℝ) * z) *
          (1 + v) ^ 7 * (20 - 17 * z) * (20 - 17 * v ^ 2 * z) := by
      field_simp [h1, h2]
    _ = _ := by rw [htail]

lemma lrLowVL7Delta_mul_base_eq_polynomial
    {v z : ℝ} (h1 : 1 + v ≠ 0) :
    lrLowDelta v ((17 / 20 : ℝ) * z) / 2 *
        (∑ k ∈ Finset.range 6,
          ((7 - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
            (v ^ 2 * ((17 / 20 : ℝ) * z)) ^ (k + 1) *
              lrLowCStarLower (7 - (k + 1))) *
        lrLowVL7CertificateBase v z =
      lrLowVL7DeltaScaledPolynomial v z := by
  unfold lrLowDelta lrLowVL7CertificateBase lrLowVL7DeltaScaledPolynomial
  dsimp only
  field_simp [h1]

lemma lrLowVL7_scaled_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVComparisonMinorant v ((17 / 20 : ℝ) * z) 7 *
        lrLowVL7CertificateBase v z = lrLowVL7Polynomial v z := by
  have hg := lrLowVG_scaled_eq_polynomial hv hz
  change lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
      lrLowVL7CertificateBase v z = lrLowVGPolynomial v z at hg
  have hc := lrLowVL7Constant_mul_base_eq_polynomial hv hz
  have hd := lrLowVL7Delta_mul_base_eq_polynomial
    (v := v) (z := z) (by linarith [hv.1])
  unfold lrLowVComparisonMinorant lrLowVL7Polynomial
  dsimp only
  norm_num only [Nat.cast_ofNat]
  calc
    (lrLowGShapeLower v (17 / 20 * z) * lrLowEHead (v ^ 2 * (17 / 20 * z)) 7 -
          7 * lrLowVConstantUpper v (17 / 20 * z) * lrLowCStarUpper 7 +
          lrLowDelta v (17 / 20 * z) / 2 *
            ∑ k ∈ Finset.range 6,
              ((7 - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
                (v ^ 2 * (17 / 20 * z)) ^ (k + 1) *
                  lrLowCStarLower (7 - (k + 1))) * lrLowVL7CertificateBase v z =
        (lrLowGShapeLower v (17 / 20 * z) * lrLowVL7CertificateBase v z) *
            lrLowEHead (v ^ 2 * (17 / 20 * z)) 7 -
          7 * (lrLowVConstantUpper v (17 / 20 * z) *
            lrLowVL7CertificateBase v z) * lrLowCStarUpper 7 +
          (lrLowDelta v (17 / 20 * z) / 2 *
            (∑ k ∈ Finset.range 6,
              ((7 - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
                (v ^ 2 * (17 / 20 * z)) ^ (k + 1) *
                  lrLowCStarLower (7 - (k + 1))) *
            lrLowVL7CertificateBase v z) := by ring
    _ = _ := by rw [hg, hc, hd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVL7_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVL7Polynomial v z *
        136011756535912857600000000000000000000000000 =
      lrLowVL7PowerEval v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  unfold lrLowVL7Polynomial lrLowVGPolynomial
    lrLowVL7ConstantScaledPolynomial lrLowVL7DeltaScaledPolynomial
    lrLowWBetaUpperNumerator lrLowWBetaNumerator
    lrLowPhiFirst12 lrLowPhiSecond12 lrLowEHead
    lrLowCStarUpper lrLowCStarLower lrLowL12 lrLowGLower
    lrLowBetaLower lrLowMinusLogLower lrAtanh5 lrLowBnUpper
    lrLowA lrLowVL7PowerEval
  unfold lrLowVL7VPowerEvalCol0 lrLowVL7VPowerEvalCol1
    lrLowVL7VPowerEvalCol2 lrLowVL7VPowerEvalCol3
    lrLowVL7VPowerEvalCol4 lrLowVL7VPowerEvalCol5
    lrLowVL7VPowerEvalCol6 lrLowVL7VPowerEvalCol7
    lrLowVL7VPowerEvalCol8 lrLowVL7VPowerEvalCol9
    lrLowVL7VPowerEvalCol10 lrLowVL7VPowerEvalCol11
    lrLowVL7VPowerEvalCol12 lrLowVL7VPowerEvalCol13
    lrLowVL7VPowerEvalCol14 lrLowVL7VPowerEvalCol15
    lrLowVL7VPowerEvalCol16 lrLowVL7VPowerEvalCol17
    lrLowVL7VPowerEvalCol18 lrLowVL7VPowerEvalCol19
    lrLowVL7VPowerEvalCol20 lrLowVL7VPowerEvalCol21
    lrLowVL7VPowerEvalCol22 lrLowVL7VPowerEvalCol23
    lrLowVL7VPowerEvalCol24 lrLowVL7VPowerEvalCol25
    lrLowVL7VPowerEvalCol26
  field_simp [hv0, h1, h2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVL7_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVComparisonMinorant v ((17 / 20 : ℝ) * z) 7 *
        lrLowVL7CertificateBase v z *
          136011756535912857600000000000000000000000000 =
      lrLowVL7PowerEval v z := by
  rw [lrLowVL7_scaled_eq_polynomial hv hz]
  exact lrLowVL7_polynomial_eq_power hv

theorem lrLowVComparisonMinorant_seven_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVComparisonMinorant v ((17 / 20 : ℝ) * z) 7 := by
  have hpower : 0 ≤ lrLowVL7PowerEval v z := by
    rw [← lrLowVL7Bernstein_eq_power]
    exact lrLowVL7Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVL7_certificate_identity hv hz
  have hvSq : v ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
      (by linarith [hv.1] : 0 ≤ 1 + v)]
  have hzv : v ^ 2 * z ≤ 1 := calc
    v ^ 2 * z ≤ 1 * z := mul_le_mul_of_nonneg_right hvSq hz.1
    _ ≤ 1 := by simpa using hz.2
  have hbase : 0 < lrLowVL7CertificateBase v z := by
    unfold lrLowVL7CertificateBase
    exact mul_pos
      (mul_pos (mul_pos (pow_pos (by linarith [hv.1]) _)
        (pow_pos (by linarith [hv.1]) _)) (by nlinarith [hz.2]))
      (by nlinarith)
  have hscale : 0 < lrLowVL7CertificateBase v z *
      (136011756535912857600000000000000000000000000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowVL7CertificateBase v z *
          136011756535912857600000000000000000000000000) *
        lrLowVComparisonMinorant v ((17 / 20 : ℝ) * z) 7 := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVComparisonMinorant_seven_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVComparisonMinorant v x 7 := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVComparisonMinorant_seven_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
