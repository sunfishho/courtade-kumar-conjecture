import InformationTheory.CourtadeKumar.GeneratedLRCompactVLowR.Certificate

/-!
# Kernel replay on the low-R, low-v part of the compact-V domain

The 1,282-leaf certificate covers `R ∈ [0,1/2]`, `v ∈ [1/3,1/2]`,
and the full high-shape interval `t² ∈ [17/20,1]`. Every leaf is checked by
ordinary kernel reduction, with no native proof dependency.
-/

namespace CourtadeKumar

abbrev lrCompactVLowRReplayBox : CertificateBox :=
  GeneratedLRCompactVLowR.rootBox

theorem lrCompactVLowRReplay_sound : LRCompactVBoxSound lrCompactVLowRReplayBox :=
  GeneratedLRCompactVLowR.target_nonnegative

/-- The production reserve on the certified rectangle, in flow coordinates. -/
theorem lrCompactVLowRReplay_flow {R v t : ℝ}
    (hR : 0 < R) (hRhi : R ≤ 1 / 2)
    (hvlo : 1 / 3 ≤ v) (hvhi : v ≤ 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hx : 17 / 20 ≤ t ^ 2)
    (hJ : 0 < lrFlowJ R v t) : 0 ≤ lrLowVReserve R v t := by
  have hRunit : R ∈ Set.Ioo (0 : ℝ) 1 := ⟨hR, by linarith⟩
  have hvunit : v ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have htAbs : |t| ≤ 1 := by
    rw [abs_of_pos ht.1]
    exact ht.2.le
  have hpoint : lrCompactVLowRReplayBox.Contains (lrCompactVFlowPoint R v t) := by
    norm_num [lrCompactVLowRReplayBox, GeneratedLRCompactVLowR.rootBox,
      CertificateBox.Contains, lrCompactVFlowPoint]
    exact ⟨hR.le, hRhi, hvlo, hvhi, hx, htAbs⟩
  have hreserve := lrCompactVLowRReplay_sound _ hpoint
    (lrCompactVFlowPoint_physical hRunit hvunit ht hJ)
  simpa only [lrCompactVReserveTarget_flow ht.1] using hreserve

end CourtadeKumar
