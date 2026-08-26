import InformationTheory.CourtadeKumar.LRSmallVZeroHead

/-!
# The zeroth small-odds coefficient

The positive first angular coefficient pays the possibly negative second one;
all later terms of `P₁` are nonnegative.  This completes the small-odds
coefficient theorem.
-/

open Set

namespace CourtadeKumar

lemma lrL_ge_quadratic
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    z ^ 2 / 2 ≤ lrL z := by
  have harg : 0 < 1 - z ^ 2 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos harg
  unfold lrL
  nlinarith

lemma lrSmallV_zero_second_term_lower
    {v : ℝ} (hv0 : 0 < v) :
    v / (12 * (1 + v)) ≤
      lrFlowBeta v * lrLowA 2 * (1 + v ^ 3) := by
  have hden : 0 < 1 + v := by linarith
  have hlogLower := Real.one_sub_inv_le_log_of_pos hden
  have hbeta : v / (1 + v) ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    convert hlogLower using 1
    field_simp [hden.ne']
    ring
  have hfactor : 0 ≤ lrLowA 2 * (1 + v ^ 3) := by
    unfold lrLowA
    positivity
  have hmul := mul_le_mul_of_nonneg_right hbeta hfactor
  unfold lrLowA at hmul ⊢
  norm_num at hmul ⊢
  have hvCube : 0 ≤ v ^ 3 := pow_nonneg hv0.le 3
  calc
    v / (12 * (1 + v)) = v / (1 + v) * (1 / 12) := by
      field_simp [hden.ne']
    _ ≤ v / (1 + v) * (1 / 12 * (1 + v ^ 3)) := by
      gcongr
      nlinarith
    _ ≤ lrFlowBeta v * (1 / 12 * (1 + v ^ 3)) := hmul
    _ = lrFlowBeta v * (1 / 12) * (1 + v ^ 3) := by ring

lemma lrSmallV_zero_two_term_margin
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1 / 3) :
    0 ≤
      (v ^ 2 / 2 * (lrG v - lrLowCStar 1 / (1 + v)) -
        lrFlowBeta v * lrFlowM v * lrLowCStar 1) +
      (lrFlowBeta v * lrLowA 2 * (1 + v ^ 3) -
        v ^ 2 * (1 + v) / 4) := by
  have hfirst := lrSmallV_zero_gamma_one_lower hv0 hv
  have hsecond := lrSmallV_zero_second_term_lower hv0
  have hvSq : v ^ 2 ≤ (1 / 9 : ℝ) := by
    have hprod : 0 ≤ ((1 / 3 : ℝ) - v) * (1 / 3 + v) :=
      mul_nonneg (sub_nonneg.mpr hv) (by linarith)
    nlinarith
  have hvCube : v ^ 3 ≤ (1 / 27 : ℝ) := by
    have hmul := mul_le_mul hvSq hv hv0.le (by norm_num : (0 : ℝ) ≤ 1 / 9)
    nlinarith
  have hpoly : 0 ≤ 10 + 27 * v - 30 * v * (1 + v) ^ 2 := by
    nlinarith [sq_nonneg v]
  have hden : 0 < 1 + v := by linarith
  have hrational : 0 ≤
      9 * v ^ 2 / (40 * (1 + v)) + v / (12 * (1 + v)) -
        v ^ 2 * (1 + v) / 4 := by
    rw [show 0 ≤
      9 * v ^ 2 / (40 * (1 + v)) + v / (12 * (1 + v)) -
        v ^ 2 * (1 + v) / 4 ↔
      0 ≤ v * (10 + 27 * v - 30 * v * (1 + v) ^ 2) by
        field_simp [hden.ne']
        constructor <;> intro h <;> nlinarith]
    exact mul_nonneg hv0.le hpoly
  linarith

theorem lrLowVConvolutionCoeff_zero_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowVConvolutionCoeff v t 0 := by
  let x : ℝ := t ^ 2
  have hx : x ∈ Icc (0 : ℝ) 1 := by
    dsimp [x]
    exact ⟨sq_nonneg t, by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]⟩
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hL := lrL_ge_quadratic (mul_nonneg hv.1.le ht.1.le) hvt
  have hf1 := lrLowVZeroF1_pos_smallV hv.1 hvSmall hx
  have hLf1 := mul_le_mul_of_nonneg_right hL hf1.le
  have hPRec := lrLowP_recursion
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩) hx 1
  have hP2 : 0 ≤ lrLowP v x 2 := lrLowP_nonneg hv.1.le hx.1 2
  have hP : lrLowA 2 * lrLowT v x 2 ≤ lrLowP v x 1 := by
    linarith
  have hbeta : 0 ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    exact (Real.log_pos (by linarith [hv.1])).le
  have hbetaP := mul_le_mul_of_nonneg_left hP hbeta
  have hgamma1 : 0 ≤
      v ^ 2 / 2 * (lrG v - lrLowCStar 1 / (1 + v)) -
        lrFlowBeta v * lrFlowM v * lrLowCStar 1 := by
    have hmargin := lrSmallV_zero_gamma_one_lower hv.1 hvSmall
    exact (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg v))
      (mul_nonneg (by norm_num) (by linarith [hv.1]))).trans hmargin
  have hsum := lrSmallV_zero_two_term_margin hv.1 hvSmall
  let γ1 : ℝ := v ^ 2 / 2 * (lrG v - lrLowCStar 1 / (1 + v)) -
    lrFlowBeta v * lrFlowM v * lrLowCStar 1
  let γ2 : ℝ := lrFlowBeta v * lrLowA 2 * (1 + v ^ 3) -
    v ^ 2 * (1 + v) / 4
  have htwo : 0 ≤ x * γ1 + x ^ 2 * γ2 := by
    have hdecomp : x * γ1 + x ^ 2 * γ2 =
        x * (1 - x) * γ1 + x ^ 2 * (γ1 + γ2) := by ring
    rw [hdecomp]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (by simpa [γ1] using hgamma1))
      (mul_nonneg (sq_nonneg x) (by simpa [γ1, γ2] using hsum))
  rw [lrLowVConvolutionCoeff_zero_eq hv ht]
  have hlower : x * γ1 + x ^ 2 * γ2 ≤
      lrL (v * t) * lrLowVZeroF1 v x +
        lrFlowBeta v * lrLowP v x 1 -
        lrFlowBeta v * lrFlowM v * x * lrLowCStar 1 := by
    have hbase :
        (v * t) ^ 2 / 2 * lrLowVZeroF1 v (t ^ 2) ≤
          lrL (v * t) * lrLowVZeroF1 v (t ^ 2) := hLf1
    have hpbase :
        lrFlowBeta v * (lrLowA 2 *
          ((t ^ 2) ^ 2 * (1 + v ^ 3))) ≤
          lrFlowBeta v * lrLowP v (t ^ 2) 1 := by
      simpa [lrLowT] using hbetaP
    have hcombined :
        (v * t) ^ 2 / 2 * lrLowVZeroF1 v (t ^ 2) +
            lrFlowBeta v * (lrLowA 2 * ((t ^ 2) ^ 2 * (1 + v ^ 3))) -
            lrFlowBeta v * lrFlowM v * t ^ 2 * lrLowCStar 1 ≤
          lrL (v * t) * lrLowVZeroF1 v (t ^ 2) +
            lrFlowBeta v * lrLowP v (t ^ 2) 1 -
            lrFlowBeta v * lrFlowM v * t ^ 2 * lrLowCStar 1 := by
      linarith
    have hid : x * γ1 + x ^ 2 * γ2 =
        (v * t) ^ 2 / 2 * lrLowVZeroF1 v (t ^ 2) +
          lrFlowBeta v * (lrLowA 2 * ((t ^ 2) ^ 2 * (1 + v ^ 3))) -
          lrFlowBeta v * lrFlowM v * t ^ 2 * lrLowCStar 1 := by
      dsimp [γ1, γ2, x]
      unfold lrLowVZeroF1 lrLowT lrLowA
      norm_num only [one_pow, Nat.cast_ofNat]
      ring
    rw [hid]
    exact hcombined
  exact htwo.trans hlower

theorem lrLowVConvolutionCoeff_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n := by
  intro n
  rcases n with _ | n
  · exact lrLowVConvolutionCoeff_zero_nonneg_smallV hv hvSmall ht
  · exact lrLowVConvolutionCoeff_posIndex_nonneg_smallV hv hvSmall ht (by omega)

end CourtadeKumar
