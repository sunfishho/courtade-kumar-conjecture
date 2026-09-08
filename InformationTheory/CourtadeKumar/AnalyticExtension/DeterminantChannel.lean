import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantCorrection
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantModel

/-! Exact collection of the finite determinant's logarithmic channel. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

noncomputable def modelGap (p : CertificatePoint) : ℝ := lrCertificateD p - lrDeterminantD1 p
noncomputable def pFactor (p : CertificatePoint) : ℝ :=
  1 - p.s + 2 * (Real.log 2 - Real.log (1 + lrCertificateV p)) + LRAnalyticMidpoint.alpha p
noncomputable def radialCost (s e c : ℝ) : ℝ :=
  s / (1 + c) * (2 * c / 7 + e * (1 - c) / 2)

lemma frozen_g {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioQ0FrozenG p = lrLowRatioNormalization p * lrLowRatioG p := by
  have h := lrLowRatioQ0G_frozen_eq_of_pos hi.1.1
    ((mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1)
    (show p.chi ∈ Icc (0 : ℝ) 1 from ⟨hi.2.2.1.le, hi.2.2.2.le⟩)
  simpa [lrLowRatioQ0FrozenG, lrLowRatioNormalization, lrLowRatioG,
    lrLowRatioLogScale, lrCertificateY0, lrCertificateE] using h

lemma frozen_omega {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioQ0FrozenOmega p = lrLowRatioNormalization p * (lrLowRatioP p - lrLowRatioG p) := by
  have h := lrLowRatioPWQ0_frozen_eq_of_physical hi.1
    ((mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1) hi.2.1.2
    (show p.chi ∈ Icc (0 : ℝ) 1 from ⟨hi.2.2.1.le, hi.2.2.2.le⟩)
  unfold lrLowRatioQ0FrozenOmega
  rw [h, lrLowerFaceOmegaQ0_zero hi.1.1]
  unfold lrLowRatioNormalization lrLowRatioP lrLowRatioG
    lrLowRatioLogScale lrSmallSBridgeS lrCertificateE
  ring

lemma omega_gap {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowerFaceOmegaQ0 p.s (lrCertificateE p) - lrLowerFaceOmegaQ0 p.s 0 =
      -lrCertificateE p / 4 * (p.s + 2 * lrCertificateD p) := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have ha : 0 < 1 + (1 - p.s) * p.k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le]
  rw [show lrCertificateE p = p.s * p.k by rfl,
    lrLowerFaceOmegaQ0_sk_eq hi.1 hk hi.2.1.2, lrLowerFaceOmegaQ0_zero hi.1.1,
    LRAnalyticMidpoint.d_formula hi, Real.log_div ha.ne' hk.ne']
  ring

lemma log_four_e {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    Real.log (4 / lrCertificateE p) = 2 * lrCertificateBFlow p + 2 * lrCertificateD p +
      2 * (Real.log 2 - Real.log (1 + lrCertificateV p)) := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  rw [LRAnalyticMidpoint.b_formula hi, LRAnalyticMidpoint.d_formula hi]
  unfold lrCertificateE lrLowRatioLogScale
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (mul_pos hi.1.1 hk).ne',
    Real.log_mul hi.1.1.ne' hk.ne',
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hi.1.1.ne', Real.log_one,
    lrSmallSBridge_log_four]
  ring

lemma frozen_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioFrozenFirstBracketNormalized p =
      lrDeterminantD1 p * pFactor p -
        lrCertificateBFlow p * (p.s + LRAnalyticMidpoint.loss p + 2 * modelGap p) := by
  unfold lrLowRatioFrozenFirstBracketNormalized
  rw [LRAnalyticMidpoint.s_identity hi, LRAnalyticMidpoint.p_identity hi]
  unfold pFactor modelGap
  ring

lemma qcore_grouped {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioQ0FirstBracketCore p =
      lrLowRatioNormalization p * lrLowRatioFrozenFirstBracketNormalized p +
      lrDeterminantD1 p * lrCertificateG0 (lrCertificateV p) +
      lrLowRatioBWeight p * (lrCertificateE p / 4 *
        (lrDeterminantD1 p * (1 - p.s + 2 * (Real.log 2 - Real.log (1 + lrCertificateV p))) -
          lrCertificateBFlow p * p.s - 2 * lrCertificateBFlow p * modelGap p)) +
      lrLowRatioKappa p *
        (lrDeterminantD1 p * lrLowerFaceQ0 (lrCertificateE p) +
          (lrCertificateBFlow p + lrDeterminantD1 p) * lrLowerFaceOmegaQ0 p.s (lrCertificateE p)) := by
  have hinner : lrDeterminantD1 p * lrLowerFaceQ0 (lrCertificateE p) +
      (lrCertificateBFlow p + lrDeterminantD1 p) *
        (lrLowerFaceOmegaQ0 p.s (lrCertificateE p) - lrLowerFaceOmegaQ0 p.s 0) =
      lrCertificateE p / 4 *
        (lrDeterminantD1 p * (1 - p.s + 2 * (Real.log 2 - Real.log (1 + lrCertificateV p))) -
          lrCertificateBFlow p * p.s - 2 * lrCertificateBFlow p * modelGap p) := by
    rw [omega_gap hi]
    unfold lrLowerFaceQ0
    rw [log_four_e hi]
    unfold modelGap
    ring
  unfold lrLowRatioQ0FirstBracketCore
  rw [lrLowRatioQ0G_eq_frozen_add_delta, lrLowRatioQ0Omega_eq_frozen_add_delta,
    frozen_g hi, frozen_omega hi, lrLowRatioQ0DeltaOmega_formula hi, ← hinner]
  unfold lrLowRatioFrozenFirstBracketNormalized lrSmallSBridgeQ0DeltaG
    lrLowRatioKappa lrLowRatioAWeight
  ring

lemma qcore_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrLowRatioNormalization p *
      (lrDeterminantD1 p * pFactor p - lrCertificateBFlow p *
        (LRAnalyticMidpoint.loss p + radialCost p.s (lrCertificateE p) p.chi +
          2 * modelGap p * (1 + lrLowRatioBWeight p / (1 + p.chi)))) ≤
      lrLowRatioQ0FirstBracketCore p + 4 * lrCertificateBFlow p * lrDeterminantDelta p *
        lrLowerFaceOmegaQ0 p.s 0 := by
  have hD := lrDeterminantD1_nonnegative hi
  have hB := (lrCertificateBFlow_pos hi).le
  have hn := lrLowRatioNormalization_pos hi
  have hd := radial_d_payment hi hs hk hD
  have hw := finite_weight_bounds hi hs hk
  have hQ := lrLowerFaceQ0_nonneg_of_mem ⟨hi.2.1.1, hi.2.1.2.le⟩
  have hOm := lrLowerFaceOmegaQ0_nonneg hi.1 hi.2.1
  have hkap := mul_nonneg hw.2.2.1
    (add_nonneg (mul_nonneg hD hQ) (mul_nonneg (add_nonneg hB hD) hOm))
  have hcorr := mul_le_mul_of_nonneg_left (delta_reserve_lower hi hs hk)
    (mul_nonneg hB hi.1.1.le)
  have hid : lrLowRatioNormalization p *
      (lrDeterminantD1 p * pFactor p - lrCertificateBFlow p *
        (LRAnalyticMidpoint.loss p + radialCost p.s (lrCertificateE p) p.chi +
          2 * modelGap p * (1 + lrLowRatioBWeight p / (1 + p.chi)))) =
      lrLowRatioNormalization p * lrLowRatioFrozenFirstBracketNormalized p +
      lrCertificateBFlow p * p.s * (lrCertificateE p / 4 *
        ((1 - p.chi) * (1 - lrCertificateE p / 2) + 12 * p.chi / 7)) -
      lrLowRatioBWeight p * lrCertificateE p / 2 * lrCertificateBFlow p * modelGap p := by
    rw [frozen_identity hi]
    unfold radialCost lrLowRatioNormalization
    field_simp [show 1 + p.chi ≠ 0 by linarith [hi.2.2.1]]
    ring
  rw [hid, qcore_grouped hi, lrLowerFaceOmegaQ0_zero hi.1.1]
  nlinarith

end CourtadeKumar.LRAnalyticDeterminant
