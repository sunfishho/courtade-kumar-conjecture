import InformationTheory.CourtadeKumar.LRSmallVTailContraction

/-!
# Assembly of the small-odds comparison tail

On `v ≤ 1/3`, the exact endpoint and the two tail contractions propagate
nonnegativity from the single entry comparison `ℒ₂` to every `ℒₙ`, `n ≥ 2`.
-/

open Set

namespace CourtadeKumar

lemma lrGShape_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrGShape t v := by
  have hbound := lrGShape_ge_tail_envelope hv ht
  have hJ : 0 ≤ Real.log 2 - topPhi t :=
    sub_nonneg.mpr (topPhi_le_log_two ⟨by linarith [ht.1], ht.2.le⟩)
  have hbeta : 0 ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    exact (Real.log_pos (by linarith [hv.1])).le
  have hL : 0 ≤ lrL (v * t) := by
    have hvt : v * t < 1 := calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
    exact lrL_nonneg (mul_nonneg hv.1.le ht.1.le) hvt
  have hratio : 0 ≤ (1 - v) / v :=
    div_nonneg (sub_nonneg.mpr hv.2.le) hv.1.le
  have hlower : 0 ≤
      2 * (Real.log 2 - topPhi t) +
        (1 - v) / v * (lrFlowBeta v + lrL (v * t)) :=
    add_nonneg (mul_nonneg (by norm_num) hJ)
      (mul_nonneg hratio (add_nonneg hbeta hL))
  exact hlower.trans hbound

theorem lrLowVComparison_nonneg_tail_smallV_of_two
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htwo : 0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) 2) :
    ∀ n : ℕ, 2 ≤ n →
      0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) n := by
  have htSq : 0 ≤ t ^ 2 := sq_nonneg t
  have htSqOne : t ^ 2 ≤ 1 := by
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hvSq : v ^ 2 ≤ (1 / 9 : ℝ) := by
    have hprod : 0 ≤ ((1 / 3 : ℝ) - v) * (1 / 3 + v) :=
      mul_nonneg (sub_nonneg.mpr hvSmall) (by linarith [hv.1])
    nlinarith
  have hξ0 : 0 ≤ v ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg v) htSq
  have hξ : v ^ 2 * t ^ 2 ≤ (1 / 9 : ℝ) := calc
    v ^ 2 * t ^ 2 ≤ v ^ 2 * 1 := mul_le_mul_of_nonneg_left htSqOne (sq_nonneg v)
    _ ≤ 1 / 9 := by simpa using hvSq
  have hξ1 : v ^ 2 * t ^ 2 < 1 := hξ.trans_lt (by norm_num)
  have hdelta : 0 ≤ lrLowDelta v (t ^ 2) := by
    unfold lrLowDelta
    have hvx : v * t ^ 2 ≤ 1 := calc
      v * t ^ 2 ≤ 1 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hv.2.le htSq
      _ ≤ 1 := by simpa using htSqOne
    exact div_nonneg (sub_nonneg.mpr hvx) (by linarith [hv.1])
  have hG : 0 ≤ lrGShape t v := lrGShape_nonneg hv ht
  have hVstar : 0 ≤ lrLowVStar v (t ^ 2) (lrGShape t v) :=
    lrLowVStar_nonneg_smallV hv hvSmall ht
  apply lrLow_tail_propagation_from_two
    (L := fun n ↦ lrLowVComparison v (t ^ 2) (lrGShape t v) n)
    (F := fun n ↦ lrLowFComparison v (t ^ 2) (lrGShape t v) n)
    (Q := lrLowQ (v ^ 2 * t ^ 2)) (R := lrLowRTail (v ^ 2 * t ^ 2))
    (Vstar := lrLowVStar v (t ^ 2) (lrGShape t v))
    (C := lrLowVComparisonConstant v (t ^ 2))
    (delta := lrLowDelta v (t ^ 2)) (G := lrGShape t v)
  · intro n hn
    exact lrLowFComparison_eq_C_alpha_sub_tails hv.1
      (sq_pos_of_pos ht.1) hξ1 hn
  · intro n hn
    unfold lrLowFComparison
    ring
  · intro n hn
    exact lrLowQ_succ_le_alphaRatio_smallXi hξ0 hξ hn
  · intro n hn
    exact lrLowRTail_succ_le_alphaRatio_smallXi hξ0 hξ hn
  · exact hdelta
  · exact hG
  · exact hVstar
  · exact htwo

end CourtadeKumar
