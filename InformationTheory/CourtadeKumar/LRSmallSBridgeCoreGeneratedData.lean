import InformationTheory.CourtadeKumar.LRSmallSBridgeFinalAssembly
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2

/-!
# Kernel-checked small-`s` replay data

The generated scalar certificate proves the four dyadic roots by transparent
replay.  This module transports that endpoint result through the existing
analytic bridge without any native evaluator.
-/

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

/-- The transparent four-root certificate transported from the finite
endpoint `L = 14 log 2` to the true logarithm `L = log (1/s)`. -/
theorem generated_frozen_core
    {s k chi : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Set.Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Set.Icc (0 : ℝ) 1) :
    (2 / 3 : ℝ) <
      lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
        (lrSmallSBridgeCoreB ⟨s, k, chi⟩) := by
  have hendpoint :=
    _root_.CourtadeKumar.LRSmallSWideLogRoundedScalarV2.four_roots_sound
      (show s ∈ Set.Icc (0 : ℝ) (1 / 16384) from ⟨hs.1.le, hs.2⟩)
      hk hchi
  rw [lrSmallSBridgeCoreTarget_eq_frozen] at hendpoint
  exact hendpoint.trans_le
    (lrSmallSBridgeFrozen_endpoint_le hs hk hchi
      (lrSmallSBridge_log_lower hs))

/-- Closed small-`s` bridge after instantiating all four generated roots. -/
theorem generated_halfMidpoint
    {s k chi : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Set.Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Set.Icc (0 : ℝ) 1) :
    (13 / 20 : ℝ) <
      lrCertificateHalfMidpointNumerator
        (⟨s, k, chi⟩ : CertificatePoint) / s := by
  let point : CertificatePoint := ⟨s, k, chi⟩
  let q0Reserve := lrSmallSBridgeChannelReserve
    (lrCertificateD point) (lrCertificateBFlow point)
    (lrCertificateV point) (lrCertificateX point)
    (lrLowerFaceOmegaQ0 point.s 0) (lrSmallSBridgeQ0G point)
    (lrLowerFacePWQ0 point.s point.k point.chi (lrCertificateV point))
  let r0Reserve := lrSmallSBridgeChannelReserve
    (lrCertificateD point) (lrCertificateBFlow point)
    (lrCertificateV point) (lrCertificateX point)
    (lrLowerFaceOmegaR0 point.s 0) (lrSmallSBridgeR0G point)
    (lrLowerFacePWR0 point.s point.k point.chi (lrCertificateV point))
  have hv := lrSmallSBridge_v_mem hs hk hchi
  have hvNe : lrCertificateV point ≠ -1 := by
    have : 0 < lrCertificateV point := by simpa [point] using hv.1
    linarith
  have hcore := generated_frozen_core hs hk hchi
  have hq0 := lrSmallSBridge_q0_restoration_lower hs hk hchi
  have hq0' :
      lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
          (lrSmallSBridgeCoreB point) - lrSmallSBridgeEpsilonV ≤
        q0Reserve / s := by
    simpa [q0Reserve, point] using hq0
  have hr0 := lrSmallSBridge_r0_restoration_lower hs hk hchi
  have hr0' : -lrSmallSBridgeEpsilonR ≤ r0Reserve / s := by
    simpa [r0Reserve, point] using hr0
  have hsplit := lrCertificateHalfMidpointNumerator_eq_q0_add_r0
    (point := point) hvNe
  have hsplitNormalized :
      lrCertificateHalfMidpointNumerator point / s =
        q0Reserve / s + r0Reserve / s := by
    rw [hsplit]
    change (q0Reserve + r0Reserve) / s = q0Reserve / s + r0Reserve / s
    ring
  have hreserve :
      lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
          (lrSmallSBridgeCoreB point) - lrSmallSBridgeEpsilonV -
          lrSmallSBridgeEpsilonR ≤
        lrCertificateHalfMidpointNumerator point / s := by
    rw [hsplitNormalized]
    linarith
  exact lrSmallSBridge_close_of_core_and_payments hcore hreserve

/-- The generated small-`s` replay discharges the removed strip in the
middle-core theorem, leaving only the compact post-bridge obligation. -/
theorem generated_middleCoreCoordinate_of_postSmallSBridge
    (hpost : LRHighShapePostSmallSBridgeMidpointCoordinateTheorem) :
    LRHighShapeMiddleCoreMidpointCoordinateTheorem := by
  intro point hinterior hrelevant hk hmiddle
  by_cases hsSmall : point.s ≤ 1 / 16384
  · have hkLower : 1 / 4 ≤ point.k := by
      rcases hmiddle with hsLarge | hkLarge
      · exfalso
        nlinarith
      · exact hkLarge.le
    have hbridge := generated_halfMidpoint
      (show point.s ∈ Set.Ioc (0 : ℝ) (1 / 16384) from
        ⟨hinterior.1.1, hsSmall⟩)
      (show point.k ∈ Set.Icc (1 / 4 : ℝ) 4 from ⟨hkLower, hk⟩)
      (show point.chi ∈ Set.Icc (0 : ℝ) 1 from
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
    have hquot : 0 < lrCertificateHalfMidpointNumerator point / point.s :=
      (show (0 : ℝ) < 13 / 20 by norm_num).trans hbridge
    have hnum : 0 < lrCertificateHalfMidpointNumerator point := by
      rw [div_pos_iff] at hquot
      rcases hquot with h | h
      · exact h.1
      · linarith [hinterior.1.1, h.2]
    unfold lrCertificateUTarget lrCertificateUDenominator
    exact (div_pos hnum (mul_pos hinterior.1.1 hinterior.2.1.1)).le
  · exact hpost point hinterior hrelevant hk hmiddle (lt_of_not_ge hsSmall)

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
