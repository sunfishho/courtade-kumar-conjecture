import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreClosure
import InformationTheory.CourtadeKumar.LRDeterminantIdealFinalRefinedReplay
import InformationTheory.CourtadeKumar.LRDeterminantLowKEntropyCoefficientRestoration
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedOneToFourRestoration

/-!
# Restricted determinant closure after the analytic inputs are proved

The refined ideal replay supplies both ideal inputs: the low-`k` replay and
the ideal margin on `1 ≤ k ≤ 4`.  Together with the analytic restoration
proved on that compact band, this removes all remaining analytic hypotheses
from the restricted determinant core.  The final Courtade--Kumar statement is
therefore reduced to four finite certificate families.
-/

namespace CourtadeKumar

/-- The ideal replay and analytic restoration prove the entire genuinely deep
determinant band left by the restricted core. -/
theorem lrDeterminantDeepOneToFour_certificate_proved :
    LRDeterminantDeepOneToFourCertificateTheorem :=
  lrDeterminantDeepOneToFour_certificate_of_ideal_and_restoration
    lrDeterminantIdealOneToFour_finalRefined_proved
    lrDeterminantDeepOneToFourRestoration_proved

/-- The refined replay also supplies the sole ideal input to the already
proved low-`k` analytic restoration. -/
theorem lrDeterminantLowKRegion_certificate_finalRefined_proved :
    LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion :=
  lrDeterminantLowKRegion_certificate_of_ideal
    lrLowKIdealReplayCertificate_finalRefined_proved

/-- Four finite certificate families now imply the target-flow numerator
theorem; no ideal or analytic restoration hypothesis remains. -/
theorem lrTargetFlowNumeratorTheorem_of_remainingRestrictedCertificates
    (compactV : LRCompactVR910ReplayLedger)
    (midpoint :
      LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) :
    LRTargetFlowNumeratorTheorem :=
  lrTargetFlowNumeratorTheorem_of_restrictedDeterminantCore
    compactV midpoint finiteV
    lrDeterminantIdealOneToFour_finalRefined_proved
    lrDeterminantDeepOneToFourRestoration_proved
    lrDeterminantLowKRegion_certificate_finalRefined_proved
    finite

/-- The remaining four finite certificate families imply the full
Courtade--Kumar statement through the proved canonical target trajectory. -/
theorem courtadeKumar_of_remainingRestrictedCertificates
    (compactV : LRCompactVR910ReplayLedger)
    (midpoint :
      LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) :
    Statement :=
  courtadeKumar_of_restrictedDeterminantCore
    compactV midpoint finiteV
    lrDeterminantIdealOneToFour_finalRefined_proved
    lrDeterminantDeepOneToFourRestoration_proved
    lrDeterminantLowKRegion_certificate_finalRefined_proved
    finite

end CourtadeKumar
