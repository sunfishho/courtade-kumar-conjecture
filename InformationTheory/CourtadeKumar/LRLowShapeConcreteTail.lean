import InformationTheory.CourtadeKumar.LRLowShapeComparisonDecomposition

/-!
# Concrete low-shape tail propagation

Given the endpoint sign `V_* ≥ 0`, the chart sign `G ≥ 0`, and the finite
entry certificate `ℒ_7 ≥ 0`, this theorem now proves every concrete comparison
coefficient from index seven onward.
-/

open Set

namespace CourtadeKumar

theorem lrLowVComparison_nonneg_tail
    {v x G : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Ioc (0 : ℝ) (17 / 20))
    (hG : 0 ≤ G) (hVstar : 0 ≤ lrLowVStar v x G)
    (hseven : 0 ≤ lrLowVComparison v x G 7) :
    ∀ n, 7 ≤ n → 0 ≤ lrLowVComparison v x G n := by
  have hxi0 : 0 ≤ v ^ 2 * x := mul_nonneg (sq_nonneg v) hx.1.le
  have hxiBound : v ^ 2 * x ≤ 17 / 20 := by
    have hvSq : v ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
        (by linarith [hv.1] : 0 ≤ 1 + v)]
    calc
      v ^ 2 * x ≤ 1 * x := mul_le_mul_of_nonneg_right hvSq hx.1.le
      _ ≤ 17 / 20 := by simpa using hx.2
  have hxi1 : v ^ 2 * x < 1 := by norm_num at hxiBound ⊢; linarith
  have hdelta : 0 ≤ lrLowDelta v x := by
    unfold lrLowDelta
    have hvx : v * x ≤ 1 := calc
      v * x ≤ 1 * x := mul_le_mul_of_nonneg_right hv.2 hx.1.le
      _ ≤ 1 := by norm_num at hx ⊢; linarith
    exact div_nonneg (sub_nonneg.mpr hvx) (by linarith [hv.1])
  apply lrLow_tail_propagation
    (L := fun n ↦ lrLowVComparison v x G n)
    (F := fun n ↦ lrLowFComparison v x G n)
    (Q := lrLowQ (v ^ 2 * x)) (R := lrLowRTail (v ^ 2 * x))
    (Vstar := lrLowVStar v x G)
    (C := lrLowVComparisonConstant v x)
    (delta := lrLowDelta v x) (G := G)
  · intro n hn
    exact lrLowFComparison_eq_C_alpha_sub_tails hv.1 hx.1 hxi1 (by omega)
  · intro n hn
    unfold lrLowFComparison
    ring
  · intro n hn
    exact lrLowQ_succ_le_alphaRatio hxi0 hxiBound hn
  · intro n hn
    exact lrLowRTail_succ_le_alphaRatio hxi0 hxiBound hn
  · exact hdelta
  · exact hG
  · exact hVstar
  · exact hseven

end CourtadeKumar
