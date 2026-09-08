import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreAssembly
import InformationTheory.CourtadeKumar.LRCanonicalTargetRootTrajectory

/-!
# Final closure from the restricted determinant core

This module keeps the determinant adapter independent of global trajectory
machinery, then packages its pointwise conclusion as the exact
`LRTargetFlowNumeratorTheorem` consumed by the proved canonical-root closure.
-/

namespace CourtadeKumar

/-- The restricted determinant inputs prove the complete pointwise target-flow
numerator theorem. -/
theorem lrTargetFlowNumeratorTheorem_of_restrictedDeterminantCore
    (compactV : LRCompactVSoundLedger)
    (midpoint :
      LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (ideal : LRDeterminantIdealOneToFourTheorem)
    (restoration : LRDeterminantDeepOneToFourRestorationTheorem)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) :
    LRTargetFlowNumeratorTheorem := by
  intro R p v t hR hp hv ht htarget
  exact lrFlowNumeratorP_nonneg_target_of_restrictedDeterminantCore
    compactV midpoint finiteV ideal restoration lowK finite
    hR hp hv ht htarget

/-- Once the restricted compact certificates are supplied, the proved
canonical target-root trajectory closes the full Courtade--Kumar statement. -/
theorem courtadeKumar_of_restrictedDeterminantCore
    (compactV : LRCompactVSoundLedger)
    (midpoint :
      LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (ideal : LRDeterminantIdealOneToFourTheorem)
    (restoration : LRDeterminantDeepOneToFourRestorationTheorem)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) :
    Statement :=
  courtadeKumar_of_targetFlow
    (lrTargetFlowNumeratorTheorem_of_restrictedDeterminantCore
      compactV midpoint finiteV ideal restoration lowK finite)

end CourtadeKumar
