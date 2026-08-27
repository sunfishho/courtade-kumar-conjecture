import InformationTheory.CourtadeKumar.LRFullFlowClosure
import InformationTheory.CourtadeKumar.LRSmallVComplete
import InformationTheory.CourtadeKumar.LRUniformTailClosure

/-!
# Compact-core assembly for the high-shape midpoint certificate

The audited finite replay uses `k = e / s`.  The analytic uniform-tail proof
closes `k ≥ 4`, so only the compact core `e ≤ 4s` remains for finite replay.
This module states that reduced interface and proves that it supplies the
exact half-midpoint hypothesis used by the final positive-flow assembly.
-/

open Set

namespace CourtadeKumar

/-- The compact part of the exact high-shape half-midpoint obligation. -/
def LRHighShapeCoreHalfMidpointTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    lrUniformTailE v t ≤ 4 * (1 - R) →
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t

/-- The compact replay and the analytic `k ≥ 4` tail exhaust the exact
high-shape half-midpoint target. -/
theorem lrHighShapeHalfMidpointTheorem_of_core
    (hcore : LRHighShapeCoreHalfMidpointTheorem) :
    LRHighShapeHalfMidpointTheorem := by
  intro R v t hR hv ht hx hvHigh hJ
  by_cases htail : 4 * (1 - R) ≤ lrUniformTailE v t
  · exact (lrUniformTail_halfMidpoint_pos hR
      (show v ∈ Ico (1 / 3 : ℝ) 1 from ⟨hvHigh, hv.2⟩)
      ht hx htail).le
  · exact hcore R v t hR hv ht hx hvHigh hJ (le_of_lt (lt_of_not_ge htail))

/-- Pointwise LR-flow closure after replacing the noncompact midpoint
certificate by its compact `k ≤ 4` part. -/
theorem lrFlowNumeratorP_nonneg_target_of_coreMidpoint_tangent
    (hcore : LRHighShapeCoreHalfMidpointTheorem)
    (htangent : LRHighShapeTangentTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t :=
  lrFlowNumeratorP_nonneg_target_of_complete_shape_halfMidpoint_T
    lrHighShapeSmallVNumeratorTheorem
    (lrHighShapeHalfMidpointTheorem_of_core hcore) htangent
    hR hp hv ht htarget

/-- Differential LR-flow closure with only the compact midpoint replay and
the tangent certificate left as hypotheses. -/
theorem hasDerivAt_lrReserve_exactFlow_of_coreMidpoint_tangent
    (hcore : LRHighShapeCoreHalfMidpointTheorem)
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
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) :=
  hasDerivAt_lrReserve_exactFlow_of_complete_shape_halfMidpoint_T
    lrHighShapeSmallVNumeratorTheorem
    (lrHighShapeHalfMidpointTheorem_of_core hcore) htangent
    hR hp hv ht hvval hvfun htarget hcurve

end CourtadeKumar
