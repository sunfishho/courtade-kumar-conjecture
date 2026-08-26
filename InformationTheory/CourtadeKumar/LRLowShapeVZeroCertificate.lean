import InformationTheory.CourtadeKumar.LRLowShapeVF1Power
import InformationTheory.CourtadeKumar.LRLowShapeVZeroPower
import InformationTheory.CourtadeKumar.LRLowShapeVZeroBridge

/-! Exact certificates for the first factor and zeroth low-shape `V` coefficient. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVF1_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVF1Minorant v ((17 / 20 : ℝ) * z) *
        lrLowWRadialBase v * 7875000 =
      lrLowVF1PowerEval v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have h4 : 4 + v * 4 ≠ 0 := by nlinarith [hv.1]
  unfold lrLowVF1Minorant lrLowGLower lrLowBetaLower
    lrLowMinusLogLower lrAtanh5 lrLowA lrLowT lrLowCStarUpper
    lrLowBnUpper lrLowWRadialBase lrLowVF1PowerEval
  unfold lrLowVF1VPowerEvalCol0 lrLowVF1VPowerEvalCol1
  unfold lrLowA
  field_simp [hv0, h1, h2, h4]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVF1_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVF1Minorant v ((17 / 20 : ℝ) * z) *
        lrLowWRadialBase v * 7875000 =
      lrLowVF1PowerEval v z :=
  lrLowVF1_polynomial_eq_power hv

theorem lrLowVF1Minorant_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVF1Minorant v ((17 / 20 : ℝ) * z) := by
  have hpower : 0 ≤ lrLowVF1PowerEval v z := by
    rw [← lrLowVF1Bernstein_eq_power]
    exact lrLowVF1Bernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVF1_certificate_identity hv (z := z)
  have hbase : 0 < lrLowWRadialBase v := by
    unfold lrLowWRadialBase
    exact mul_pos (pow_pos (by linarith [hv.1]) _)
      (pow_pos (by linarith [hv.1]) _)
  have hscale : 0 < lrLowWRadialBase v * (7875000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowWRadialBase v * 7875000) *
        lrLowVF1Minorant v ((17 / 20 : ℝ) * z) := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVF1Minorant_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVF1Minorant v x := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVF1Minorant_nonneg_certificate hv hz using 1 <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
lemma lrLowVZero_polynomial_eq_power
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVZeroMinorant v ((17 / 20 : ℝ) * z) *
        lrLowWRadialBase v *
          1015917686784000000000000000000 =
      lrLowVZeroPowerEval v z := by
  have hv0 : v ≠ 0 := hv.1.ne'
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have hdenUpper : (1 + v) * (2 + v) ^ 9 ≠ 0 :=
    mul_ne_zero h1 (pow_ne_zero 9 h2)
  have hupperEq :
      lrAtanh5Upper (v / (2 + v)) =
        lrLowWBetaUpperNumerator v / ((1 + v) * (2 + v) ^ 9) :=
    (eq_div_iff hdenUpper).2 (by
      simpa [mul_assoc] using lrAtanh5Upper_mul_denominator h1 h2)
  unfold lrLowVZeroMinorant lrLowVF1Minorant lrLowL12
    lrLowGLower lrLowBetaLower lrLowMinusLogLower lrAtanh5
    lrLowP1Lower lrLowA lrLowT lrFlowM
    lrLowCStarUpper lrLowBnUpper lrLowWRadialBase
    lrLowVZeroPowerEval
  rw [hupperEq]
  unfold lrLowWBetaUpperNumerator lrLowWBetaNumerator
  unfold lrLowVZeroVPowerEvalCol0 lrLowVZeroVPowerEvalCol1
    lrLowVZeroVPowerEvalCol2 lrLowVZeroVPowerEvalCol3
    lrLowVZeroVPowerEvalCol4 lrLowVZeroVPowerEvalCol5
    lrLowVZeroVPowerEvalCol6 lrLowVZeroVPowerEvalCol7
    lrLowVZeroVPowerEvalCol8 lrLowVZeroVPowerEvalCol9
    lrLowVZeroVPowerEvalCol10 lrLowVZeroVPowerEvalCol11
    lrLowVZeroVPowerEvalCol12 lrLowVZeroVPowerEvalCol13
  unfold lrLowA
  field_simp [hv0, h1, h2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

lemma lrLowVZero_certificate_identity
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVZeroMinorant v ((17 / 20 : ℝ) * z) *
        lrLowWRadialBase v *
          1015917686784000000000000000000 =
      lrLowVZeroPowerEval v z :=
  lrLowVZero_polynomial_eq_power hv

theorem lrLowVZeroMinorant_nonneg_certificate
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowVZeroMinorant v ((17 / 20 : ℝ) * z) := by
  have hpower : 0 ≤ lrLowVZeroPowerEval v z := by
    rw [← lrLowVZeroBernstein_eq_power]
    exact lrLowVZeroBernstein_nonneg
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩) hz
  have hid := lrLowVZero_certificate_identity hv (z := z)
  have hbase : 0 < lrLowWRadialBase v := by
    unfold lrLowWRadialBase
    exact mul_pos (pow_pos (by linarith [hv.1]) _)
      (pow_pos (by linarith [hv.1]) _)
  have hscale : 0 < lrLowWRadialBase v *
      (1015917686784000000000000000000 : ℝ) :=
    mul_pos hbase (by norm_num)
  have hprod : 0 ≤
      (lrLowWRadialBase v * 1015917686784000000000000000000) *
        lrLowVZeroMinorant v ((17 / 20 : ℝ) * z) := by
    rw [mul_comm, ← mul_assoc, hid]
    exact hpower
  exact nonneg_of_mul_nonneg_right hprod hscale

theorem lrLowVZeroMinorant_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) (17 / 20)) :
    0 ≤ lrLowVZeroMinorant v x := by
  have hz : (20 * x / 17 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2]
  convert lrLowVZeroMinorant_nonneg_certificate hv hz using 1 <;> ring

theorem lrLowVConvolutionCoeff_zero_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVConvolutionCoeff v t 0 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hf1 := lrLowVF1Minorant_nonneg hvIoc hxIcc
  have hzero := lrLowVZeroMinorant_nonneg hvIoc hxIcc
  exact hzero.trans (lrLowVZeroMinorant_le_coefficient hv ht hf1)

end CourtadeKumar
