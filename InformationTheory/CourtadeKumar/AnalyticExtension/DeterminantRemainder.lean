import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantChannel
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointEndpointBudget

/-! The only adverse entropy contribution has an explicit rational budget. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

noncomputable def entropyCost (s e c C : ℝ) : ℝ :=
  s ^ 2 * C / (14 * (1 + c)) * (2 * e + 64 / 7)

lemma b_ge_d1 {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) : lrDeterminantD1 p ≤ lrCertificateBFlow p := by
  have hx : lrCertificateX p ≤ 1 := sub_le_self _ (mul_nonneg hi.2.2.1.le hi.2.1.1.le)
  have hB := (lrCertificateBFlow_pos hi).le
  have hJ := hr.2
  unfold lrCertificateJ at hJ
  have hm := mul_le_mul_of_nonneg_left hx hB
  linarith [lrDeterminantD1_le_D hi]

lemma remainder_omega_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioKappa p * lrLowerFaceOmegaR0 p.s 0 ≤ lrLowRatioR0Omega p := by
  have hv := lrCertificateV_mem_Ioo hi
  have h := LRAnalyticMidpoint.pwR0_lower hi
  have hid : lrLowRatioKappa p * lrLowerFaceOmegaR0 p.s 0 =
      (1 + 1 / lrCertificateV p) * lrLowerFaceOmegaR0 p.s 0 -
        4 * lrLowerFaceOmegaR0 p.s 0 / (1 + lrCertificateV p) := by
    unfold lrLowRatioKappa lrLowRatioAWeight lrLowRatioBWeight
    ring
  rw [hid]
  unfold lrLowRatioR0Omega
  linarith

lemma rcore_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    -lrLowRatioNormalization p * lrCertificateBFlow p *
      entropyCost p.s (lrCertificateE p) p.chi (Real.log (4 / p.s)) ≤
      lrLowRatioR0FirstBracketCore p +
        4 * lrCertificateBFlow p * lrDeterminantDelta p * lrLowerFaceOmegaR0 p.s 0 := by
  let B := lrCertificateBFlow p
  let D := lrDeterminantD1 p
  let e := lrCertificateE p
  let kap := lrLowRatioKappa p
  let delta := lrDeterminantDelta p
  let W := lrLowerFaceOmegaR0 p.s 0
  let C := Real.log (4 / p.s)
  have hB : 0 ≤ B := (lrCertificateBFlow_pos hi).le
  have hD : 0 ≤ D := lrDeterminantD1_nonnegative hi
  have hDB : D ≤ B := b_ge_d1 hi hr
  have he : 0 ≤ e := hi.2.1.1.le
  have hw := finite_weight_bounds hi hs hk
  have hdel : delta ≤ 4 / 7 * e := delta_upper hi hs hk
  have hdel0 : 0 ≤ delta := lrDeterminantDelta_nonnegative hi
  have hW : W ≤ 0 := lrLowerFaceOmegaR0_zero_nonpos hi.1
  have hWlo : -(p.s ^ 2 / 14 * C) ≤ W := LRAnalyticMidpoint.omega_zero_lower ⟨hi.1.1, hs⟩
  have hcoef0 : 0 ≤ (B + D) * kap + 4 * B * delta := by
    exact add_nonneg (mul_nonneg (add_nonneg hB hD) hw.2.2.1)
      (mul_nonneg (mul_nonneg (by norm_num) hB) hdel0)
  have hcoef : (B + D) * kap + 4 * B * delta ≤ B * e ^ 2 / 2 + 16 / 7 * B * e := by
    have h1 := mul_le_mul_of_nonneg_left hw.2.2.2 (add_nonneg hB hD)
    have h2 := mul_le_mul_of_nonneg_right hDB (sq_nonneg e)
    have h3 := mul_le_mul_of_nonneg_left hdel (show 0 ≤ 4 * B by positivity)
    dsimp [B, D, e, kap, delta] at *
    nlinarith
  have hC : 0 ≤ C := by linarith [LRAnalyticMidpoint.log_four_div_ge ⟨hi.1.1, hs⟩]
  have hcoefU : 0 ≤ B * e ^ 2 / 2 + 16 / 7 * B * e := by positivity
  have h1 := mul_le_mul_of_nonpos_right hcoef hW
  have h2 := mul_le_mul_of_nonneg_left hWlo hcoefU
  have h3 := mul_le_mul_of_nonneg_left (remainder_omega_lower hi) (add_nonneg hB hD)
  have hG := mul_nonneg hD (lrLowRatioR0G_nonnegative hi)
  have hid : -lrLowRatioNormalization p * B * entropyCost p.s e p.chi C =
      (B * e ^ 2 / 2 + 16 / 7 * B * e) * -(p.s ^ 2 / 14 * C) := by
    unfold lrLowRatioNormalization entropyCost
    change -(e * (1 + p.chi) / 4) * B *
      (p.s ^ 2 * C / (14 * (1 + p.chi)) * (2 * e + 64 / 7)) = _
    field_simp [show 1 + p.chi ≠ 0 by linarith [hi.2.2.1]]
    ring
  change -lrLowRatioNormalization p * B * entropyCost p.s e p.chi C ≤ _
  rw [hid]
  unfold lrLowRatioR0FirstBracketCore
  dsimp [B, D, e, kap, delta, W, C] at *
  nlinarith

end CourtadeKumar.LRAnalyticDeterminant
