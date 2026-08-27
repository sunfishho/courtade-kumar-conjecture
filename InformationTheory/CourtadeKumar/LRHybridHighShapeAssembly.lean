import InformationTheory.CourtadeKumar.LRCompactVCorrelatedReplayLedger
import InformationTheory.CourtadeKumar.LRSmallVComplete
import InformationTheory.CourtadeKumar.LRFullFlowAssembly

/-!
# Hybrid high-shape assembly

The compact `V` ledger is strongest away from the endpoint, while the
cancellation-coordinate midpoint and tangent evaluators are designed for
`R` close to one.  This module partitions at `R = 9/10`: the existing direct
`V` argument handles the compact side, leaving midpoint and tangent
certificates only on the near-endpoint side.
-/

open Set

namespace CourtadeKumar

def LRHighShapeNearEndpointHalfMidpointTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    9 / 10 < R →
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t

def LRHighShapeNearEndpointTangentTheorem : Prop :=
  ∀ (R v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    17 / 20 ≤ t ^ 2 →
    1 / 3 ≤ v →
    0 < lrFlowJ R v t →
    9 / 10 < R →
    0 ≤ lrFlowTReserve R v t

/-- The compact direct-`V` ledger and the two near-endpoint certificates
exhaust the high-shape positive-flow chart. -/
theorem lrFlowNumeratorP_nonneg_target_of_compactV_and_nearEndpoint
    (ledger : LRCompactVR910ReplayLedger)
    (hmidpoint : LRHighShapeNearEndpointHalfMidpointTheorem)
    (htangent : LRHighShapeNearEndpointTangentTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  by_cases htLow : t ^ 2 ≤ 17 / 20
  · exact lrFlowNumeratorP_nonneg_target_lowShape
      hR hp hv ht htLow htarget
  have htHigh : 17 / 20 ≤ t ^ 2 := by linarith
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target
      hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
      hR hv ht hJzero
  · by_cases hvSmall : v ≤ 1 / 3
    · exact lrHighShapeSmallVNumeratorTheorem
        R p v t hR hp hv ht htHigh hvSmall hJpos htarget
    have hvHigh : 1 / 3 ≤ v := by linarith
    by_cases hcompact : R ≤ 9 / 10
    · have hV := ledger.v_nonnegative R v t hR hcompact hv hvHigh ht
        htHigh hJpos
      exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
        hR hp hv ht htarget hJpos hV
    · have hnear : 9 / 10 < R := lt_of_not_ge hcompact
      exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_T
        hR hp hv ht htarget hJpos
        (hmidpoint R v t hR hv ht htHigh hvHigh hJpos hnear)
        (htangent R v t hR hv ht htHigh hvHigh hJpos hnear)

end CourtadeKumar
