import InformationTheory.CourtadeKumar.LRNearEndpointMidpointAssembly
import InformationTheory.CourtadeKumar.LRNearEndpointTangentAssembly

/-!
# Reduced end-to-end LR certificate interface

All analytic tails and exact coordinate changes are assembled here.  The
complete LR derivative closure now depends on precisely three finite-data
interfaces: the compact `V` replay ledger through `R=9/10`, a bounded
near-endpoint midpoint strip, and a bounded near-endpoint tangent chart.
-/

open Set

namespace CourtadeKumar

open LRSmallSBridgeCoreCertificate

theorem lrFlowNumeratorP_nonneg_target_of_reduced_certificates
    (ledger : LRCompactVR910ReplayLedger)
    (hmidpoint :
      LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (htangent : LRHighShapeNearEndpointTangentCoordinateTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t :=
  lrFlowNumeratorP_nonneg_target_of_compactV_and_nearEndpoint ledger
    (nearEndpointHalfMidpoint_of_postSmallSBridge hmidpoint)
    (nearEndpointTangentTheorem_of_coordinateTheorem htangent)
    hR hp hv ht htarget

theorem hasDerivAt_lrReserve_exactFlow_of_reduced_certificates
    (ledger : LRCompactVR910ReplayLedger)
    (hmidpoint :
      LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (htangent : LRHighShapeNearEndpointTangentCoordinateTheorem)
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
  hasDerivAt_lrReserve_exactFlow_of_compactV_and_nearEndpoint ledger
    (nearEndpointHalfMidpoint_of_postSmallSBridge hmidpoint)
    (nearEndpointTangentTheorem_of_coordinateTheorem htangent)
    hR hp hv ht hvval hvfun htarget hcurve

end CourtadeKumar
