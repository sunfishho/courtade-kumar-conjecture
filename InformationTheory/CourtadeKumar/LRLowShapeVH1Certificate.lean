import InformationTheory.CourtadeKumar.LRLowShapeVH1Power
import InformationTheory.CourtadeKumar.LRLowShapeVHeadPolynomialBridge

/-! Exact semantic certificate for the first finite low-shape `V` head. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVH1_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVHeadPolynomial v z 2 *
        832239769013452800000000000000000000000000 =
      lrLowVH1PowerEval v z := by
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
    lrLowPnLower lrLowT lrLowA lrLowVH1PowerEval
  unfold lrLowVH1VPowerEvalCol0 lrLowVH1VPowerEvalCol1
    lrLowVH1VPowerEvalCol2 lrLowVH1VPowerEvalCol3
    lrLowVH1VPowerEvalCol4 lrLowVH1VPowerEvalCol5
    lrLowVH1VPowerEvalCol6 lrLowVH1VPowerEvalCol7
    lrLowVH1VPowerEvalCol8 lrLowVH1VPowerEvalCol9
    lrLowVH1VPowerEvalCol10 lrLowVH1VPowerEvalCol11
    lrLowVH1VPowerEvalCol12 lrLowVH1VPowerEvalCol13
    lrLowVH1VPowerEvalCol14 lrLowVH1VPowerEvalCol15
    lrLowVH1VPowerEvalCol16 lrLowVH1VPowerEvalCol17
    lrLowVH1VPowerEvalCol18 lrLowVH1VPowerEvalCol19
    lrLowVH1VPowerEvalCol20 lrLowVH1VPowerEvalCol21
    lrLowVH1VPowerEvalCol22 lrLowVH1VPowerEvalCol23
    lrLowVH1VPowerEvalCol24 lrLowVH1VPowerEvalCol25
    lrLowVH1VPowerEvalCol26
  field_simp [hv0, h1, h2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVH1_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 2 *
        lrLowVL7CertificateBase v z *
          832239769013452800000000000000000000000000 =
      lrLowVH1PowerEval v z := by
  rw [lrLowVHeadMinorant_mul_base_eq_polynomial hv hz]
  exact lrLowVH1_polynomial_eq_power hv

theorem lrLowVHeadMinorant_two_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 2 := by
  have hpower : 0 ≤ lrLowVH1PowerEval v z := by
    rw [← lrLowVH1Bernstein_eq_power]
    exact lrLowVH1Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVH1_certificate_identity hv hz
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
      (832239769013452800000000000000000000000000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowVL7CertificateBase v z *
          832239769013452800000000000000000000000000) *
        lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) 2 := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVHeadMinorant_two_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVHeadMinorant v x 2 := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVHeadMinorant_two_nonneg_certificate hv hz using 1 <;> ring

end CourtadeKumar
