import InformationTheory.CourtadeKumar.LRLowShapeVMinorantBridge

/-!
# Analytic bridge for the zeroth low-shape `V` coefficient

This isolates the exact zeroth coefficient, its first factor, and the rational
minorant used by the finite Bernstein certificate.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowVZeroF1 (v x : ℝ) : ℝ :=
  lrG v - lrLowA 1 * lrLowT v x 1 - lrLowCStar 1 / (1 + v)

noncomputable def lrLowVF1Minorant (v x : ℝ) : ℝ :=
  lrLowGLower v - lrLowA 1 * lrLowT v x 1 -
    lrLowCStarUpper 1 / (1 + v)

noncomputable def lrLowVZeroMinorant (v x : ℝ) : ℝ :=
  lrLowL12 (v ^ 2 * x) * lrLowVF1Minorant v x +
    lrLowBetaLower v * lrLowP1Lower v x -
    lrAtanh5Upper (v / (2 + v)) * lrFlowM v * x *
      lrLowCStarUpper 1

lemma lrLowVConvolutionCoeff_zero_eq
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowVConvolutionCoeff v t 0 =
      lrL (v * t) * lrLowVZeroF1 v (t ^ 2) +
        lrFlowBeta v * lrLowP v (t ^ 2) 1 -
        lrFlowBeta v * lrFlowM v * t ^ 2 * lrLowCStar 1 := by
  have hsplit := lrGShape_add_p_one hv
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  unfold lrLowVConvolutionCoeff
  norm_num [lrLowDFlowCoeff, lrLowBFlowCoeff, lrLowFDerivCoeff,
    lrLowYTangentCoeff]
  rw [hsplit]
  unfold lrFlowA lrLowVZeroF1 lrLowCStar
  ring

lemma lrLowVF1Minorant_le
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVF1Minorant v x ≤ lrLowVZeroF1 v x := by
  have hden : 0 ≤ 1 + v := by linarith [hv.1]
  have hc := div_le_div_of_nonneg_right (lrLowCStar_le_upper 1) hden
  have hg := lrLowGLower_le_lrG hv
  unfold lrLowVF1Minorant lrLowVZeroF1
  linarith

lemma lrLowL12_le_lrL
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowL12 (v ^ 2 * t ^ 2) ≤ lrL (v * t) := by
  have hvt : 0 < v * t := mul_pos hv.1 ht.1
  have hvt1 : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hq : v ^ 2 * t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    constructor
    · positivity
    · nlinarith [mul_pos hvt (sub_pos.mpr hvt1)]
  have hL := lrL_sqrt_partial_sum_le hq 12
  rw [lrLow_sqrt_sq_product hv.1.le ht.1.le] at hL
  simpa [lrLowL12] using hL

theorem lrLowVZeroMinorant_le_coefficient
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hf1 : 0 ≤ lrLowVF1Minorant v (t ^ 2)) :
    lrLowVZeroMinorant v (t ^ 2) ≤
      lrLowVConvolutionCoeff v t 0 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have hxClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg t
    · nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hvt0 : 0 ≤ v * t := mul_nonneg hv.1.le ht.1.le
  have hvt1 : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hL := lrLowL12_le_lrL hv ht
  have hL0 := lrLowL12_nonneg
    (mul_nonneg (sq_nonneg v) (sq_nonneg t))
  have hLActual0 := lrL_nonneg hvt0 hvt1
  have hf1le := lrLowVF1Minorant_le (x := t ^ 2) hvIoc
  have hf1Actual0 := hf1.trans hf1le
  have hLf1 := mul_le_mul hL hf1le hf1 hLActual0
  have hbeta := lrAtanh5_beta_bounds hvIoc
  have hbetaLower0 := lrLowBetaLower_nonneg hvIoc
  have hbetaActual0 : 0 ≤ lrFlowBeta v := by
    simpa [lrFlowBeta] using hbetaLower0.trans hbeta.1
  have hbetaUpper0 : 0 ≤ lrAtanh5Upper (v / (2 + v)) :=
    hbetaActual0.trans (by simpa [lrFlowBeta] using hbeta.2)
  have hp := lrLowP1Lower_le hvClosed hxClosed
  have hp0 := lrLowP1Lower_nonneg hv.1.le (sq_nonneg t)
  have hbetaP := mul_le_mul hbeta.1 hp hp0 hbetaActual0
  have hbetaP' :
      lrLowBetaLower v * lrLowP1Lower v (t ^ 2) ≤
        lrFlowBeta v * lrLowP v (t ^ 2) 1 := by
    simpa [lrLowBetaLower, lrFlowBeta] using hbetaP
  have hc := lrLowCStar_le_upper 1
  have hc0 : 0 ≤ lrLowCStar 1 := by
    unfold lrLowCStar
    exact mul_nonneg (by norm_num) (lrLowB_pos 1).le
  have hbetaC :
      lrFlowBeta v * lrLowCStar 1 ≤
        lrAtanh5Upper (v / (2 + v)) * lrLowCStarUpper 1 :=
    mul_le_mul (by simpa [lrFlowBeta] using hbeta.2) hc hc0 hbetaUpper0
  have hMx : 0 ≤ lrFlowM v * t ^ 2 := by
    unfold lrFlowM
    exact mul_nonneg (div_nonneg hv.1.le (by linarith [hv.1])) (sq_nonneg t)
  have hnegative := mul_le_mul_of_nonneg_right hbetaC hMx
  have hnegative' :
      lrFlowBeta v * lrFlowM v * t ^ 2 * lrLowCStar 1 ≤
        lrAtanh5Upper (v / (2 + v)) * lrFlowM v * t ^ 2 *
          lrLowCStarUpper 1 := by
    convert hnegative using 1 <;> ring
  rw [lrLowVConvolutionCoeff_zero_eq hv ht]
  unfold lrLowVZeroMinorant
  linarith

end CourtadeKumar
