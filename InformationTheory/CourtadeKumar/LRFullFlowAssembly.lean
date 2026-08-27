import InformationTheory.CourtadeKumar.LRLowShapeFlowClosure
import InformationTheory.CourtadeKumar.LRDirectVAssembly

/-!
# Exhaustive LR flow partition

This module isolates the three exact high-shape certificate interfaces left
after the complete low-shape proof and assembles them with the already proved
negative- and zero-flow charts.
-/

open Set

namespace CourtadeKumar

/-- The direct `V ≥ 0` branch for positive flow and small target odds. -/
def LRHighShapeSmallVNumeratorTheorem : Prop :=
  ∀ (R p v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    v ≤ 1 / 3 →
    0 < lrFlowJ R v t →
    lrPrefixEll R p = lrSquareTarget R v t →
    0 ≤ lrFlowNumeratorP R p v t

/-- The independent high-shape midpoint certificate `(U)`. -/
def LRHighShapeMidpointTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    0 ≤ lrFlowUReserve R v t

/-- The high-shape tangent/determinant certificate `(T)`. -/
def LRHighShapeTangentTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    0 ≤ lrFlowTReserve R v t

/-- The cancellation-preserving determinant certificate used in the final
high-shape ledger.  Its target is the outer-midpoint flow numerator; unlike
the separate `(U)` and `(T)` interfaces, one proof of this reserve closes the
entire positive-`J` chart directly. -/
def LRHighShapeVTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    0 ≤ lrLowVReserve R v t

theorem lrFlowNumeratorP_nonneg_target_of_highShape_certificates
    (hsmall : LRHighShapeSmallVNumeratorTheorem)
    (hmidpoint : LRHighShapeMidpointTheorem)
    (htangent : LRHighShapeTangentTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htHigh : 17 / 20 ≤ t ^ 2)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target
      hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
      hR hv ht hJzero
  · by_cases hvSmall : v ≤ 1 / 3
    · exact hsmall R p v t hR hp hv ht htHigh hvSmall hJpos htarget
    · exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_U_T
        hR hp hv ht htarget hJpos
          (hmidpoint R v t hR hv ht htHigh (by linarith) hJpos)
          (htangent R v t hR hv ht htHigh (by linarith) hJpos)

theorem lrFlowNumeratorP_nonneg_target_of_complete_shape_certificates
    (hsmall : LRHighShapeSmallVNumeratorTheorem)
    (hmidpoint : LRHighShapeMidpointTheorem)
    (htangent : LRHighShapeTangentTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  by_cases htLow : t ^ 2 ≤ 17 / 20
  · exact lrFlowNumeratorP_nonneg_target_lowShape
      hR hp hv ht htLow htarget
  · exact lrFlowNumeratorP_nonneg_target_of_highShape_certificates
      hsmall hmidpoint htangent hR hp hv ht (by linarith) htarget

/-- A single high-shape `V` certificate replaces the independent midpoint
and tangent certificates.  This is the formal counterpart of the audited
identity `U = s² V + 2 M W J`: at the outer midpoint, `s² V` is exactly the
flow numerator, and positive `J` makes the numerator improve as the target
probability moves left. -/
theorem lrFlowNumeratorP_nonneg_target_of_highShape_V
    (hsmall : LRHighShapeSmallVNumeratorTheorem)
    (hV : LRHighShapeVTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htHigh : 17 / 20 ≤ t ^ 2)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target
      hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
      hR hv ht hJzero
  · by_cases hvSmall : v ≤ 1 / 3
    · exact hsmall R p v t hR hp hv ht htHigh hvSmall hJpos htarget
    · exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
        hR hp hv ht htarget hJpos
          (hV R v t hR hv ht htHigh (by linarith) hJpos)

/-- Exhaustive flow closure using the low-shape analytic proof and one
high-shape cancellation-preserving determinant certificate. -/
theorem lrFlowNumeratorP_nonneg_target_of_complete_shape_V
    (hsmall : LRHighShapeSmallVNumeratorTheorem)
    (hV : LRHighShapeVTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  by_cases htLow : t ^ 2 ≤ 17 / 20
  · exact lrFlowNumeratorP_nonneg_target_lowShape
      hR hp hv ht htLow htarget
  · exact lrFlowNumeratorP_nonneg_target_of_highShape_V
      hsmall hV hR hp hv ht (by linarith) htarget

end CourtadeKumar
