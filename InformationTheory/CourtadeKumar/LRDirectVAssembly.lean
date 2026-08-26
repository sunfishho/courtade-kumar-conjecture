import InformationTheory.CourtadeKumar.LRLowShapeTAlgebra

/-!
# Direct closure of positive LR flow from the `V` reserve

The analytic `V` reserve is exactly the flow numerator at the outer
midpoint.  On the positive-`J` branch the numerator decreases with the input
probability, while physical target matching puts that probability to the
left of the midpoint.  Consequently `V ≥ 0` closes the flow directly,
without either the midpoint `(U)` or tangent `(T)` certificate.
-/

open Set

namespace CourtadeKumar

theorem lrFlowTargetProbability_le_midpoint_of_J_pos
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    p ≤ lrFlowM v := by
  have hM : lrFlowM v ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) :=
    lrFlowM_mem_Ioc
      (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hgap : 0 ≤ lrFlowGap R v t := lrFlowGap_nonneg hR hv ht
  have hgapValue : lrFlowGap R v t =
      lrPrefixEll R p - lrPrefixEll R (lrFlowM v) := by
    unfold lrFlowGap
    rw [htarget]
  by_contra hnot
  have hMp : lrFlowM v < p := lt_of_not_ge hnot
  have hstrict := (strictAntiOn_lrPrefixEll hR) hM hp hMp
  linarith

/-- Equation `(13b)` of the direct LR assembly. -/
theorem lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hJ : 0 < lrFlowJ R v t)
    (hV : 0 ≤ lrLowVReserve R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  have hpM := lrFlowTargetProbability_le_midpoint_of_J_pos
    hR hp hv ht htarget
  have hW : 0 < lrWKernel R 1 := lrWKernel_one_pos hR
  have hsub := lrFlowNumeratorP_sub R (lrFlowM v) p v t
  have hH : lrFlowH R v t = -lrFlowJ R v t :=
    lrFlowH_eq_negJ R v t
  rw [hH, lrFlowNumeratorP_midpoint_eq_lrLowVReserve
    (by linarith [hv.1])] at hsub
  have hmove : 0 ≤
      4 * lrWKernel R 1 * lrFlowJ R v t * (lrFlowM v - p) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hW.le) hJ.le)
      (sub_nonneg.mpr hpM)
  nlinarith

end CourtadeKumar
