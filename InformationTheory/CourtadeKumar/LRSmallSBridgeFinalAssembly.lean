import InformationTheory.CourtadeKumar.LRSmallSBridgeRemainderIdentification
import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreReplayAssembly

/-! Final analytic assembly of the small-`s` bridge, manuscript (M30)--(M33). -/

open Set

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

/-- Once the four finite replay roots pass the Boolean checker, the actual
half-midpoint numerator has the strict M33 margin throughout the small-`s`
bridge. -/
theorem halfMidpoint_of_four_roots
    (terms sqrtFuel logFuel : ℕ)
    {tree0 tree1 tree2 tree3 : SubdivisionCertificate Unit Unit}
    (h0 : tree0.check (autoAccepts terms sqrtFuel logFuel) noDiscard
      (rootBox (1 / 4) (1 / 2)) = true)
    (h1 : tree1.check (autoAccepts terms sqrtFuel logFuel) noDiscard
      (rootBox (1 / 2) 1) = true)
    (h2 : tree2.check (autoAccepts terms sqrtFuel logFuel) noDiscard
      (rootBox 1 2) = true)
    (h3 : tree3.check (autoAccepts terms sqrtFuel logFuel) noDiscard
      (rootBox 2 4) = true)
    {s k chi : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
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
  have hcore := frozen_core_of_four_roots terms sqrtFuel logFuel
    h0 h1 h2 h3 hs hk hchi
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

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
