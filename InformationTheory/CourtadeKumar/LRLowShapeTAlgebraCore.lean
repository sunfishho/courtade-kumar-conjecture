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

end CourtadeKumar
