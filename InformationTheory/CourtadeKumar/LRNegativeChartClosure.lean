import InformationTheory.CourtadeKumar.LRNegativeGapComparison

/-! Assumption-free closure of the nonpositive-`J` LR flow charts. -/

open Set

namespace CourtadeKumar

/-- The negative-`J` chart, with all tangent estimates discharged. -/
theorem lrFlowNumeratorP_nonneg_of_J_neg_target
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hJ : lrFlowJ R v t < 0) :
    0 ≤ lrFlowNumeratorP R p v t := by
  let g := lrFlowGap R v t
  let q₀ := lrFlowQ₀ R v
  have hM := lrFlowM_mem_Ioc
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hg : 0 ≤ g := lrFlowGap_nonneg hR hv ht
  have hCge : g ≤ lrFlowC R v t := lrFlowGap_le_lrFlowC hR hv ht
  have hq₀ : 0 < q₀ := lrFlowQ₀_pos hR
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hq₀Delta : 4 * lrBDelta R ≤ q₀ := four_delta_le_lrFlowQ₀ hR
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  have hgapValue : g = lrPrefixEll R p - lrPrefixEll R (lrFlowM v) := by
    unfold g lrFlowGap
    rw [htarget]
  have hTangent : lrFlowM v - g / q₀ ≤ p :=
    lrPrefix_tangent_lower_bound
      (show R ∈ Icc (0 : ℝ) 1 from ⟨hR.1.le, hR.2.le⟩)
      hp hM hg hq₀ hgapValue (by rfl)
  exact lrFlowNumeratorP_nonneg_of_J_neg_physical hR hv ht hJ
    hg hCge hq₀ hq₀Delta hTangent

/-- Both nonpositive-`J` charts are now closed. -/
theorem lrFlowNumeratorP_nonneg_of_J_nonpos_target
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hJ : lrFlowJ R v t ≤ 0) :
    0 ≤ lrFlowNumeratorP R p v t := by
  rcases hJ.lt_or_eq with hJneg | hJzero
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical hR hv ht hJzero

end CourtadeKumar
