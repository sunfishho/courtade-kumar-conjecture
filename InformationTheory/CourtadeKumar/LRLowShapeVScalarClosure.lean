import InformationTheory.CourtadeKumar.LRLowShapeVCoefficientReduction

/-!
# Closure of the low-shape `V` coefficients from scalar comparisons

The remaining certificate obligations are precisely the zeroth coefficient
and the family of manuscript comparisons `L_n ≥ 0` for `n ≥ 2`.
-/

open Set

namespace CourtadeKumar

lemma lrFlowA_pos
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < lrFlowA v t := by
  have hbeta : 0 < lrFlowBeta v := by
    unfold lrFlowBeta
    exact Real.log_pos (by linarith [hv.1])
  have hvt0 : 0 ≤ v * t := mul_nonneg hv.1.le ht.1.le
  have hvt1 : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hL : 0 ≤ lrL (v * t) := lrL_nonneg hvt0 hvt1
  unfold lrFlowA
  linarith

lemma lrLowP_nonneg
    {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ lrLowP v x n := by
  unfold lrLowP
  exact tsum_nonneg fun k ↦ mul_nonneg
    (lrLowA_pos (by omega)).le (lrLowT_nonneg hv hx _)

theorem lrLowVConvolutionCoeff_nonneg_of_comparisons
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hzero : 0 ≤ lrLowVConvolutionCoeff v t 0)
    (hcomparison : ∀ n : ℕ, 2 ≤ n →
      0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) n) :
    ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n := by
  intro n
  rcases n with _ | n
  · exact hzero
  · have hid := lrLowVConvolutionCoeff_pred_eq_comparison
      (v := v) (t := t) ht.1.le (n := n + 2) (by omega)
    rw [show n + 2 - 1 = n + 1 by omega] at hid
    rw [hid]
    exact add_nonneg (hcomparison (n + 2) (by omega))
      (mul_nonneg
        (mul_nonneg (by positivity) (lrFlowA_pos hv ht).le)
        (lrLowP_nonneg hv.1.le (sq_nonneg t) (n + 2)))

theorem lrFlowNumeratorP_nonneg_target_lowShape_of_V_comparisons
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ))
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hzero : 0 ≤ lrLowVConvolutionCoeff v t 0)
    (hcomparison : ∀ n : ℕ, 2 ≤ n →
      0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) n) :
    0 ≤ lrFlowNumeratorP R p v t := by
  exact lrFlowNumeratorP_nonneg_target_lowShape_of_coeff_nonneg
    hR hp hv ht htSq htarget
      (lrLowVConvolutionCoeff_nonneg_of_comparisons
        hv ht hzero hcomparison)

end CourtadeKumar
