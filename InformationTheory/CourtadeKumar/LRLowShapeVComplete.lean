import InformationTheory.CourtadeKumar.LRLowShapeVScalarClosure
import InformationTheory.CourtadeKumar.LRLowShapeVHeadBridge
import InformationTheory.CourtadeKumar.LRLowShapeVTailAssembly
import InformationTheory.CourtadeKumar.LRLowShapeVZeroCertificate

/-! Complete coefficientwise closure of the low-shape `V` reserve. -/

open Set

namespace CourtadeKumar

theorem lrLowVConvolutionCoeff_nonneg_lowShape
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n := by
  intro n
  by_cases hn : n ≤ 5
  · interval_cases n
    · exact lrLowVConvolutionCoeff_zero_nonneg hv ht htSq
    · exact lrLowVConvolutionCoeff_one_nonneg hv ht htSq
    · exact lrLowVConvolutionCoeff_two_nonneg hv ht htSq
    · exact lrLowVConvolutionCoeff_three_nonneg hv ht htSq
    · exact lrLowVConvolutionCoeff_four_nonneg hv ht htSq
    · exact lrLowVConvolutionCoeff_five_nonneg hv ht htSq
  · have hn6 : 6 ≤ n := by omega
    have hid := lrLowVConvolutionCoeff_pred_eq_comparison
      (v := v) (t := t) ht.1.le (n := n + 1) (by omega)
    rw [show n + 1 - 1 = n by omega] at hid
    rw [hid]
    exact add_nonneg
      (lrLowVComparison_nonneg_tail_lowShape hv ht htSq (n + 1) (by omega))
      (mul_nonneg
        (mul_nonneg (by positivity) (lrFlowA_pos hv ht).le)
        (lrLowP_nonneg hv.1.le (sq_nonneg t) (n + 1)))

theorem lrFlowNumeratorP_nonneg_target_lowShape
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ))
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  exact lrFlowNumeratorP_nonneg_target_lowShape_of_coeff_nonneg
    hR hp hv ht htSq htarget
      (lrLowVConvolutionCoeff_nonneg_lowShape hv ht htSq)

end CourtadeKumar
