import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreAutoTree

/-! Assembly of the four dyadic roots in the compact M30 replay. -/

open Set

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

theorem rootBox_contains
    {s k chi : ℝ} {kLo kHi : ℚ}
    (hs : s ∈ Icc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (kLo : ℝ) (kHi : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (rootBox kLo kHi).Contains ⟨s, k, chi⟩ := by
  have h : (0 : ℝ) ≤ s ∧ s ≤ 1 / 16384 ∧
      (kLo : ℝ) ≤ k ∧ k ≤ (kHi : ℝ) ∧
      (0 : ℝ) ≤ chi ∧ chi ≤ 1 :=
    ⟨hs.1, hs.2, hk.1, hk.2, hchi.1, hchi.2⟩
  simpa [rootBox, CertificateBox.Contains] using h

/-- A checked tree for each dyadic `k` band proves the endpoint core over
the entire compact box from (M30). -/
theorem four_roots_sound
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
    (hs : s ∈ Icc (0 : ℝ) (1 / 16384))
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (hchi : chi ∈ Icc (0 : ℝ) 1) :
    (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget ⟨s, k, chi⟩ := by
  by_cases hk0 : k ≤ 1 / 2
  · exact subdivision_sound terms sqrtFuel logFuel h0 _
      (rootBox_contains hs (by norm_num; exact ⟨hk.1, hk0⟩) hchi)
  · have hk0' : 1 / 2 < k := lt_of_not_ge hk0
    by_cases hk1 : k ≤ 1
    · exact subdivision_sound terms sqrtFuel logFuel h1 _
        (rootBox_contains hs (by norm_num; exact ⟨hk0'.le, hk1⟩) hchi)
    · have hk1' : 1 < k := lt_of_not_ge hk1
      by_cases hk2 : k ≤ 2
      · exact subdivision_sound terms sqrtFuel logFuel h2 _
          (rootBox_contains hs (by norm_num; exact ⟨hk1'.le, hk2⟩) hchi)
      · exact subdivision_sound terms sqrtFuel logFuel h3 _
          (rootBox_contains hs
            (by norm_num; exact ⟨(lt_of_not_ge hk2).le, hk.2⟩) hchi)

/-- The positive logarithmic slope transports M30 from the finite endpoint
to the true value `L = log (1/s)`. -/
theorem frozen_core_of_four_roots
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
    (2 / 3 : ℝ) <
      lrSmallSBridgeFrozen s k chi (Real.log (1 / s))
        (lrSmallSBridgeCoreB ⟨s, k, chi⟩) := by
  have hendpoint := four_roots_sound terms sqrtFuel logFuel h0 h1 h2 h3
    (show s ∈ Icc (0 : ℝ) (1 / 16384) from ⟨hs.1.le, hs.2⟩) hk hchi
  rw [lrSmallSBridgeCoreTarget_eq_frozen] at hendpoint
  exact hendpoint.trans_le
    (lrSmallSBridgeFrozen_endpoint_le hs hk hchi
      (lrSmallSBridge_log_lower hs))

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
