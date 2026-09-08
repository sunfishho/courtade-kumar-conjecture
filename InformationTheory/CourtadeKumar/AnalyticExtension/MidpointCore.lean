import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointBudget

/-! A pointwise logarithmic alternative to the full midpoint evaluator.
It keeps the entropy payment dependent on the actual point. -/
namespace CourtadeKumar.LRAnalyticMidpoint

noncomputable def entropyPayment (p : CertificatePoint) : ℝ :=
  (5 / 42 : ℝ) * lrCertificateBFlow p * p.s * Real.log (4 / p.s)

noncomputable def coreTarget (p : CertificatePoint) : ℝ := frozen p - entropyPayment p

theorem numerator_pointwise_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    p.s * coreTarget p ≤ lrCertificateHalfMidpointNumerator p := by
  have hq := q0_restoration hi hr hs hk
  rw [frozen_identity hi] at hq
  have hr0 := channel_r0_lower hi hr hs hk
  have hw := omega_zero_lower ⟨hi.1.1, hs⟩
  have hscaled := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 3) (lrCertificateBFlow_pos hi).le)
  rw [lrCertificateHalfMidpointNumerator_eq_q0_add_r0
    (by linarith [(lrCertificateV_mem_Ioo hi).1] : lrCertificateV p ≠ -1)]
  unfold coreTarget entropyPayment
  nlinarith

/-- This target has logarithms and algebraic coordinates, but no binary
entropy evaluations, entropy derivatives, or interval channel restoration. -/
theorem midpoint_of_core {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4)
    (hcore : 0 ≤ coreTarget p) : 0 ≤ lrCertificateUTarget p := by
  have h := numerator_pointwise_lower hi hr hs hk
  have h0 := mul_nonneg hi.1.1.le hcore
  unfold lrCertificateUTarget lrCertificateUDenominator
  exact div_nonneg (h0.trans h) (mul_nonneg hi.1.1.le hi.2.1.1.le)

end CourtadeKumar.LRAnalyticMidpoint
