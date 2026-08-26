import InformationTheory.CourtadeKumar.LRDirectVAssembly
import InformationTheory.CourtadeKumar.LRFullFlowAssembly
import InformationTheory.CourtadeKumar.LRSmallVExceptionalIndices

/-!
# Exact endpoint of the analytic small-odds coefficient proof

The remaining analytic work in the small-`v` chart is stated directly at the
coefficient level.  Once those coefficients are nonnegative, the convergent
series gives `V ≥ 0`, and the direct midpoint identity closes the physical
flow numerator without `(U)` or `(T)`.
-/

open Set

namespace CourtadeKumar

def LRSmallVCoefficientTheorem : Prop :=
  ∀ (v t : ℝ),
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    v ≤ 1 / 3 →
    ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n

theorem lrHighShapeSmallVNumerator_of_coefficients
    (hcoeff : LRSmallVCoefficientTheorem) :
    LRHighShapeSmallVNumeratorTheorem := by
  intro R p v t hR hp hv ht _htHigh hvSmall hJ htarget
  have hV : 0 ≤ lrLowVReserve R v t :=
    lrLowVReserve_nonneg_of_coeff_nonneg hR hv ht
      (hcoeff v t hv ht hvSmall)
  exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
    hR hp hv ht htarget hJ hV

end CourtadeKumar
