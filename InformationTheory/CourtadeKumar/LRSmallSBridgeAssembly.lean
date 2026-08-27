import InformationTheory.CourtadeKumar.LRSmallSBridgeRemainderLoss

/-! Assembly arithmetic for the small-`s` bridge, manuscript (M33). -/

namespace CourtadeKumar

lemma lrSmallSBridge_payment_arithmetic :
    (13 / 20 : ℝ) <
      2 / 3 - lrSmallSBridgeEpsilonV - lrSmallSBridgeEpsilonR := by
  unfold lrSmallSBridgeEpsilonV lrSmallSBridgeEpsilonR
  norm_num

lemma lrSmallSBridge_payment_value :
    (2 / 3 : ℝ) - lrSmallSBridgeEpsilonV - lrSmallSBridgeEpsilonR =
      119009744083 / 179404800000 := by
  unfold lrSmallSBridgeEpsilonV lrSmallSBridgeEpsilonR
  norm_num

/-- Once the exact frozen replay (M30) and the two exact subtraction
identities are connected, the rational payments close the bridge with the
strict margin stated in (M33). -/
theorem lrSmallSBridge_close_of_core_and_payments
    {core reserve : ℝ}
    (hcore : (2 / 3 : ℝ) < core)
    (hreserve : core - lrSmallSBridgeEpsilonV -
        lrSmallSBridgeEpsilonR ≤ reserve) :
    (13 / 20 : ℝ) < reserve := by
  have hmargin := lrSmallSBridge_payment_arithmetic
  linarith

end CourtadeKumar
