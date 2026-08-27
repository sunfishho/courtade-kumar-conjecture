import InformationTheory.CourtadeKumar.LRFullFlowAssembly

/-!
# Differential closure of the complete LR target-root flow

This module turns the exhaustive pointwise numerator theorem into the exact
nonnegative derivative statement needed for integration along a regular
target-root trajectory.  The only remaining inputs are the three high-shape
certificates isolated in `LRFullFlowAssembly`.
-/

open Set

namespace CourtadeKumar

theorem hasDerivAt_lrReserve_exactFlow_of_complete_shape_certificates
    (hsmall : LRHighShapeSmallVNumeratorTheorem)
    (hmidpoint : LRHighShapeMidpointTheorem)
    (htangent : LRHighShapeTangentTheorem)
    {R p v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvval : vfun R = v) (hvfun : HasDerivAt vfun v' R)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hcurve :
      (fun y : ℝ ↦ lrSquareTarget y (vfun y) t) =ᶠ[nhds R]
        (fun y : ℝ ↦ lrSquareObjective y (lrProbabilityToOdds p))) :
    HasDerivAt
        (fun y : ℝ ↦
          lrSquareReserve y (lrProbabilityToOdds p) (vfun y) t)
        (lrFlowNumerator R (lrProbabilityToOdds p) v t /
          (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2)) R ∧
      0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) := by
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) := by
    calc
      lrGShape (Real.sqrt R * t) v = lrSquareTarget R v t := rfl
      _ = lrPrefixEll R p := htarget.symm
      _ = lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) :=
        lrPrefixEll_eq_lrObjectiveTarget hR hp
  have hderiv := hasDerivAt_lrReserve_exactFlow hR hu.1 hv.1 ht hvt
    hvval hvfun hroot hcurve
  have hpOdds : lrFlowP (lrProbabilityToOdds p) = p := by
    simpa [lrFlowP, lrOddsToProbability] using
      lrOddsToProbability_probabilityToOdds
        (show p < 1 from hp.2.trans (by norm_num))
  have hnumP :=
    lrFlowNumeratorP_nonneg_target_of_complete_shape_certificates
      hsmall hmidpoint htangent hR
      (show p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) from ⟨hp.1, hp.2.le⟩)
      hv ht htarget
  have hnum : 0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t := by
    rw [lrFlowNumerator_eq_p, hpOdds]
    exact hnumP
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hden : 0 < lrFlowB R v t * (1 - R) ^ 2 * t ^ 2 :=
    mul_pos (mul_pos hB (sq_pos_of_pos (sub_pos.mpr hR.2)))
      (sq_pos_of_pos ht.1)
  exact ⟨hderiv, div_nonneg hnum hden.le⟩

/-- Differential closure using the exact half-midpoint target certified by
the audited high-shape ledger. -/
theorem hasDerivAt_lrReserve_exactFlow_of_complete_shape_halfMidpoint_T
    (hsmall : LRHighShapeSmallVNumeratorTheorem)
    (hmidpoint : LRHighShapeHalfMidpointTheorem)
    (htangent : LRHighShapeTangentTheorem)
    {R p v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvval : vfun R = v) (hvfun : HasDerivAt vfun v' R)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hcurve :
      (fun y : ℝ ↦ lrSquareTarget y (vfun y) t) =ᶠ[nhds R]
        (fun y : ℝ ↦ lrSquareObjective y (lrProbabilityToOdds p))) :
    HasDerivAt
        (fun y : ℝ ↦
          lrSquareReserve y (lrProbabilityToOdds p) (vfun y) t)
        (lrFlowNumerator R (lrProbabilityToOdds p) v t /
          (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2)) R ∧
      0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) := by
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) := by
    calc
      lrGShape (Real.sqrt R * t) v = lrSquareTarget R v t := rfl
      _ = lrPrefixEll R p := htarget.symm
      _ = lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) :=
        lrPrefixEll_eq_lrObjectiveTarget hR hp
  have hderiv := hasDerivAt_lrReserve_exactFlow hR hu.1 hv.1 ht hvt
    hvval hvfun hroot hcurve
  have hpOdds : lrFlowP (lrProbabilityToOdds p) = p := by
    simpa [lrFlowP, lrOddsToProbability] using
      lrOddsToProbability_probabilityToOdds
        (show p < 1 from hp.2.trans (by norm_num))
  have hnumP :=
    lrFlowNumeratorP_nonneg_target_of_complete_shape_halfMidpoint_T
      hsmall hmidpoint htangent hR
      (show p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) from ⟨hp.1, hp.2.le⟩)
      hv ht htarget
  have hnum : 0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t := by
    rw [lrFlowNumerator_eq_p, hpOdds]
    exact hnumP
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hden : 0 < lrFlowB R v t * (1 - R) ^ 2 * t ^ 2 :=
    mul_pos (mul_pos hB (sq_pos_of_pos (sub_pos.mpr hR.2)))
      (sq_pos_of_pos ht.1)
  exact ⟨hderiv, div_nonneg hnum hden.le⟩

end CourtadeKumar
