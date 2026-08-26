import InformationTheory.CourtadeKumar.LRSmallVComplete
import InformationTheory.CourtadeKumar.LRFullFlowClosure

/-!
# Full LR flow after closing the small-odds branch

Only the two large-odds, high-shape certificates `(U)` and `(T)` remain as
inputs to the exhaustive LR differential theorem.
-/

open Set

namespace CourtadeKumar

theorem lrFlowNumeratorP_nonneg_target_of_midpoint_tangent
    (hmidpoint : LRHighShapeMidpointTheorem)
    (htangent : LRHighShapeTangentTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t :=
  lrFlowNumeratorP_nonneg_target_of_complete_shape_certificates
    lrHighShapeSmallVNumeratorTheorem hmidpoint htangent
      hR hp hv ht htarget

theorem hasDerivAt_lrReserve_exactFlow_of_midpoint_tangent
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
        (fun y : ℝ ↦ lrSquareReserve y (lrProbabilityToOdds p) (vfun y) t)
        (lrFlowNumerator R (lrProbabilityToOdds p) v t /
          (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2)) R ∧
      0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) :=
  hasDerivAt_lrReserve_exactFlow_of_complete_shape_certificates
    lrHighShapeSmallVNumeratorTheorem hmidpoint htangent
      hR hp hv ht hvval hvfun htarget hcurve

end CourtadeKumar
