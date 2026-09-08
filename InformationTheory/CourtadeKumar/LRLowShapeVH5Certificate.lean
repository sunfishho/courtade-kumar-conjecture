import InformationTheory.CourtadeKumar.LRLowShapeVH5Power
import InformationTheory.CourtadeKumar.NativePolynomialNormalization
import InformationTheory.CourtadeKumar.LRLowShapeVHeadPolynomialBridge

/-! Exact semantic certificate for the fifth finite low-shape `V` head. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVH5_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVHeadPolynomial v z 6 *
        3051545819715993600000000000000000000000000 =
      lrLowVH5PowerEval v z := by
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
    lrLowPnLower lrLowT lrLowA lrLowVH5PowerEval
  unfold lrLowVH5VPowerEvalCol0 lrLowVH5VPowerEvalCol1
    lrLowVH5VPowerEvalCol2 lrLowVH5VPowerEvalCol3
    lrLowVH5VPowerEvalCol4 lrLowVH5VPowerEvalCol5
    lrLowVH5VPowerEvalCol6 lrLowVH5VPowerEvalCol7
    lrLowVH5VPowerEvalCol8 lrLowVH5VPowerEvalCol9
    lrLowVH5VPowerEvalCol10 lrLowVH5VPowerEvalCol11
    lrLowVH5VPowerEvalCol12 lrLowVH5VPowerEvalCol13
    lrLowVH5VPowerEvalCol14 lrLowVH5VPowerEvalCol15
    lrLowVH5VPowerEvalCol16 lrLowVH5VPowerEvalCol17
    lrLowVH5VPowerEvalCol18 lrLowVH5VPowerEvalCol19
    lrLowVH5VPowerEvalCol20 lrLowVH5VPowerEvalCol21
    lrLowVH5VPowerEvalCol22 lrLowVH5VPowerEvalCol23
    lrLowVH5VPowerEvalCol24 lrLowVH5VPowerEvalCol25
    lrLowVH5VPowerEvalCol26
  field_simp [hv0, h1, h2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVH5_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 6 *
        lrLowVL7CertificateBase v z *
          3051545819715993600000000000000000000000000 =
      lrLowVH5PowerEval v z := by
  rw [lrLowVHeadMinorant_mul_base_eq_polynomial hv hz]
  exact lrLowVH5_polynomial_eq_power hv

theorem lrLowVHeadMinorant_six_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 6 := by
  have hpower : 0 ≤ lrLowVH5PowerEval v z := by
    rw [← lrLowVH5Bernstein_eq_power]
    exact lrLowVH5Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVH5_certificate_identity hv hz
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
      (3051545819715993600000000000000000000000000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowVL7CertificateBase v z *
          3051545819715993600000000000000000000000000) *
        lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 6 := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVHeadMinorant_six_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVHeadMinorant v x 6 := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVHeadMinorant_six_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
