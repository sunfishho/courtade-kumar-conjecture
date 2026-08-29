import InformationTheory.CourtadeKumar.LRDeterminantRestrictedOneToFourFiniteStage
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedOneToFourTrueChannelRestoration
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedOneToFourRestorationEndpoints

/-!
# Fully analytic restricted bounded-deep restoration

This module composes the independently developed finite,
true-channel, entropy/coefficient, and direct-remainder stages.  Its sole
export is the exact restoration theorem required by the restricted CK core on
`1 <= k <= 4`; no certificate or additional analytic hypothesis remains.
-/

namespace CourtadeKumar

open LRRestrictedOneToFourFiniteStage

theorem lrDeterminantDeepOneToFourRestoration_proved :
    LRDeterminantDeepOneToFourRestorationTheorem :=
  lrDeterminantDeepOneToFourRestoration_of_firstTwoStages
    { finite := finiteLow_oneToFour
      channelPayments := fun point hinterior hrelevant hdeep _hkOne hkFour =>
        lrOneToFour_trueChannelPayments hinterior hrelevant hdeep hkFour
      channelEndpoint := fun point hinterior hdeep _hkOne hkFour =>
        lrOneToFour_channelPointwiseLoss_le_lowEndpoint
          hinterior hdeep hkFour }

end CourtadeKumar
