import InformationTheory.CourtadeKumar.LRLowShapeVH2Power
import InformationTheory.CourtadeKumar.NativePolynomialNormalization
import InformationTheory.CourtadeKumar.LRLowShapeVHeadPolynomialBridge

/-! Exact semantic certificate for the second finite low-shape `V` head. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVH2_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVHeadPolynomial v z 3 *
        554826512675635200000000000000000000000000 =
      lrLowVH2PowerEval v z := by
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
    lrLowPnLower lrLowT lrLowA lrLowVH2PowerEval
  unfold lrLowVH2VPowerEvalCol0 lrLowVH2VPowerEvalCol1
    lrLowVH2VPowerEvalCol2 lrLowVH2VPowerEvalCol3
    lrLowVH2VPowerEvalCol4 lrLowVH2VPowerEvalCol5
    lrLowVH2VPowerEvalCol6 lrLowVH2VPowerEvalCol7
    lrLowVH2VPowerEvalCol8 lrLowVH2VPowerEvalCol9
    lrLowVH2VPowerEvalCol10 lrLowVH2VPowerEvalCol11
    lrLowVH2VPowerEvalCol12 lrLowVH2VPowerEvalCol13
    lrLowVH2VPowerEvalCol14 lrLowVH2VPowerEvalCol15
    lrLowVH2VPowerEvalCol16 lrLowVH2VPowerEvalCol17
    lrLowVH2VPowerEvalCol18 lrLowVH2VPowerEvalCol19
    lrLowVH2VPowerEvalCol20 lrLowVH2VPowerEvalCol21
    lrLowVH2VPowerEvalCol22 lrLowVH2VPowerEvalCol23
    lrLowVH2VPowerEvalCol24 lrLowVH2VPowerEvalCol25
    lrLowVH2VPowerEvalCol26
  field_simp [hv0, h1, h2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVH2_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 3 *
        lrLowVL7CertificateBase v z *
          554826512675635200000000000000000000000000 =
      lrLowVH2PowerEval v z := by
  rw [lrLowVHeadMinorant_mul_base_eq_polynomial hv hz]
  exact lrLowVH2_polynomial_eq_power hv

theorem lrLowVHeadMinorant_three_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 3 := by
  have hpower : 0 ≤ lrLowVH2PowerEval v z := by
    rw [← lrLowVH2Bernstein_eq_power]
    exact lrLowVH2Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVH2_certificate_identity hv hz
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
      (554826512675635200000000000000000000000000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowVL7CertificateBase v z *
          554826512675635200000000000000000000000000) *
        lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 3 := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVHeadMinorant_three_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVHeadMinorant v x 3 := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVHeadMinorant_three_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
