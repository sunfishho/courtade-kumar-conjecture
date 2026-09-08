import InformationTheory.CourtadeKumar.PerspectiveWeakDualCore
import InformationTheory.CourtadeKumar.Statement

/-! Public-statement wrapper for finite ordered-triangle weak duality. -/

open scoped NNReal BigOperators

namespace CourtadeKumar

/-- Consequently, affine support certificates at every admissible channel
imply the full Courtade--Kumar theorem. -/
theorem courtadeKumar_of_orderedTriangleAffineSupport
    (hsupport : ∀ (alpha : ℝ≥0), (alpha : ℝ) ≤ 1 / 2 →
      OrderedTriangleAffineSupportTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_orderedEqualMultiplier
  intro alpha halpha
  exact orderedEqualMultiplier_of_orderedTriangle alpha
    (orderedTriangleBellmanStep_of_affineSupport alpha (hsupport alpha halpha))

end CourtadeKumar
