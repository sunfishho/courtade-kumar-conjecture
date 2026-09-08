import InformationTheory.CourtadeKumar.AnalyticExtension.DirectVRestoration
import InformationTheory.CourtadeKumar.LRHighShapeMidpointVFallback

/-! A completely analytic replacement for all twenty-two finite low-ratio
V certificate roots. No numerical certificate or native computation is used. -/
namespace CourtadeKumar.LRLowRatioDirectV

lemma target_decomposition {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrCertificateVTarget p = q0Core p + r0Core p +
      4 * lrCertificateBFlow p * lrDeterminantDelta p * lrCertificateW p := by
  have hv := lrCertificateV_mem_Ioo hi
  rw [lrCertificateVTarget_eq_firstBracket_add (by linarith [hv.1]),
    lrLowRatioFirstBracket_eq_q0_add_r0_add_atom]
  unfold lrLowRatioQ0FirstBracketCore lrLowRatioR0FirstBracketCore lrDeterminantPsi
  rw [lrCertificateGShape_eq_smallSBridge_split,
    lrCertificatePW_eq_smallSBridge_split,
    lrCertificateW_eq_smallSBridge_split]
  unfold q0Core r0Core lrLowRatioQ0Omega lrLowRatioR0Omega
  ring

/-- Uniform positive margin for the exact direct-V target on the full
low-ratio near-endpoint strip. Relevance is not needed for this stronger result. -/
theorem normalized_margin {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) :
    (1 / 50 : ℝ) < lrCertificateVTarget p / lrLowRatioNormalization p := by
  have hq := q0_restoration hi hk hs
  have hr := r0_restoration hi hk hs
  have hf := frozen_margin hi hk hs
  have hn := lrLowRatioNormalization_pos hi
  have hpay : (1 / 50 : ℝ) < 3 / 140 - epsilonEntropy := by
    norm_num [epsilonEntropy]
  have hscaled := mul_lt_mul_of_pos_left hf hn
  have hatom : 0 ≤
      4 * lrCertificateBFlow p * lrDeterminantDelta p * lrCertificateW p :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (lrCertificateBFlow_pos hi).le)
        (lrDeterminantDelta_nonnegative hi))
      (lrCertificateW_pos hi).le
  have hpayScaled := mul_lt_mul_of_pos_left hpay hn
  rw [lt_div_iff₀ hn, target_decomposition hi]
  nlinarith

theorem vTarget_positive {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) : 0 < lrCertificateVTarget p := by
  have hm := normalized_margin hi hk hs
  have hn := lrLowRatioNormalization_pos hi
  have hp : 0 < lrCertificateVTarget p / lrLowRatioNormalization p := by linarith
  have h := mul_pos hp hn
  rw [div_mul_cancel₀ _ hn.ne'] at h
  exact h

/-- The complete formerly open finite-V certificate interface. -/
theorem finiteV : LRDeterminantLowRatioFiniteVTargetTheorem := by
  intro p hi _hr hk _hsLo hsHi
  exact (vTarget_positive hi hk hsHi).le

theorem midpoint_nonnegative {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p)
    (hk : LRDeterminantLowRatioRegion p) (hs : p.s ≤ 1 / 10) :
    0 ≤ lrCertificateUTarget p :=
  lrCertificateUTarget_nonnegative_of_VTarget hi hr (vTarget_positive hi hk hs).le

end CourtadeKumar.LRLowRatioDirectV
