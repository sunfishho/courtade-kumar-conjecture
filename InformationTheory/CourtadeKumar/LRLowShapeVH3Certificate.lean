import InformationTheory.CourtadeKumar.LRLowShapeVH3Power
import InformationTheory.CourtadeKumar.NativePolynomialNormalization
import InformationTheory.CourtadeKumar.LRLowShapeVHeadPolynomialBridge

/-! Exact semantic certificate for the third finite low-shape `V` head. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVH3_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVHeadPolynomial v z 4 *
        416119884506726400000000000000000000000000 =
      lrLowVH3PowerEval v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  unfold lrLowVHeadPolynomial lrLowVComparisonScaledPolynomial
    lrLowVDeltaScaledPolynomial lrLowVL7ConstantScaledPolynomial
    lrLowVGPolynomial lrLowWALowerRadialNumerator
    lrLowWRadialBase
    lrLowWBetaUpperNumerator lrLowWBetaNumerator
    lrLowPhiFirst12 lrLowPhiSecond12 lrLowEHead
    lrLowCStarUpper lrLowCStarLower lrLowL12 lrLowGLower
    lrLowBetaLower lrLowMinusLogLower lrAtanh5 lrLowBnUpper
    lrLowPnLower lrLowT lrLowA lrLowVH3PowerEval
  unfold lrLowVH3VPowerEvalCol0 lrLowVH3VPowerEvalCol1
    lrLowVH3VPowerEvalCol2 lrLowVH3VPowerEvalCol3
    lrLowVH3VPowerEvalCol4 lrLowVH3VPowerEvalCol5
    lrLowVH3VPowerEvalCol6 lrLowVH3VPowerEvalCol7
    lrLowVH3VPowerEvalCol8 lrLowVH3VPowerEvalCol9
    lrLowVH3VPowerEvalCol10 lrLowVH3VPowerEvalCol11
    lrLowVH3VPowerEvalCol12 lrLowVH3VPowerEvalCol13
    lrLowVH3VPowerEvalCol14 lrLowVH3VPowerEvalCol15
    lrLowVH3VPowerEvalCol16 lrLowVH3VPowerEvalCol17
    lrLowVH3VPowerEvalCol18 lrLowVH3VPowerEvalCol19
    lrLowVH3VPowerEvalCol20 lrLowVH3VPowerEvalCol21
    lrLowVH3VPowerEvalCol22 lrLowVH3VPowerEvalCol23
    lrLowVH3VPowerEvalCol24 lrLowVH3VPowerEvalCol25
    lrLowVH3VPowerEvalCol26
  field_simp [hv0, h1, h2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVH3_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 4 *
        lrLowVL7CertificateBase v z *
          416119884506726400000000000000000000000000 =
      lrLowVH3PowerEval v z := by
  rw [lrLowVHeadMinorant_mul_base_eq_polynomial hv hz]
  exact lrLowVH3_polynomial_eq_power hv

theorem lrLowVHeadMinorant_four_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 4 := by
  have hpower : 0 ≤ lrLowVH3PowerEval v z := by
    rw [← lrLowVH3Bernstein_eq_power]
    exact lrLowVH3Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVH3_certificate_identity hv hz
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
      (416119884506726400000000000000000000000000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowVL7CertificateBase v z *
          416119884506726400000000000000000000000000) *
        lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 4 := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVHeadMinorant_four_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVHeadMinorant v x 4 := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVHeadMinorant_four_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
