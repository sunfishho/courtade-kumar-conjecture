import InformationTheory.CourtadeKumar.LRFlowCharts

/-!
# Lightweight core of the low-shape tangent algebra

The compact-`V` certificate needs only the two grouped reserve definitions
from `LRLowShapeTAlgebra`.  Keeping them in this small dependency core avoids
pulling the unrelated low-shape `U` certificate (including its very large
tensor-Bernstein objects) into every compact-`V` semantic check.
-/

namespace CourtadeKumar

noncomputable def lrLowYTangent (R v t : ℝ) : ℝ :=
  lrFlowPW R v t -
    4 * lrWKernel R 1 * lrFlowM v * t ^ 2

noncomputable def lrLowVReserve (R v t : ℝ) : ℝ :=
  lrFlowD R v t * lrFlowC R v t +
    lrFlowB R v t * lrLowYTangent R v t

/-- The flow numerator at the outer midpoint is exactly the grouped `V`
reserve.  This elementary identity belongs in the lightweight core: direct
interval evaluators need it to identify their target, but do not need any of
the low-shape certificate machinery. -/
lemma lrFlowNumeratorP_midpoint_eq_lrLowVReserve
    {R v t : ℝ} (hv : v ≠ -1) :
    lrFlowNumeratorP R (lrFlowM v) v t =
      lrLowVReserve R v t := by
  unfold lrFlowNumeratorP lrLowVReserve lrLowYTangent lrFlowC
    lrFlowD lrFlowA lrFlowM
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  field_simp [hden]
  ring

end CourtadeKumar
