import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointBudget
import InformationTheory.CourtadeKumar.AnalyticExtension.DirectV

/-! Analytic replacement of the whole k≤1/4 part of the remaining midpoint
family, extending its former lower-face cutoff from 1/128 to 1/10. -/
open Set
namespace CourtadeKumar.LRAnalyticMidpoint

lemma d_formula {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrCertificateD p =
      (Real.log (1 + (1 - p.s) * p.k) - Real.log p.k) / 2 := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have ha : 0 < 1 + (1 - p.s) * p.k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le]
  have hY : lrDeterminantY p = (1 + (1 - p.s) * p.k) / p.k := by
    unfold lrDeterminantY lrCertificateB lrCertificateE
    field_simp [hi.1.1.ne', hk.ne']
  rw [lrCertificateD_eq_half_log_determinantY hi, hY, Real.log_div ha.ne' hk.ne']
  ring

lemma b_formula {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrCertificateBFlow p = lrLowRatioLogScale p / 2 +
      Real.log (1 + lrCertificateV p) - Real.log (1 + (1 - p.s) * p.k) / 2 := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have ha : 0 < 1 + (1 - p.s) * p.k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le]
  have hb : lrCertificateB p.s (lrCertificateE p) = p.s * (1 + (1 - p.s) * p.k) := by
    unfold lrCertificateB lrCertificateE
    ring
  unfold lrCertificateBFlow lrCertificateBFlowValue lrLowRatioLogScale
  rw [hb, Real.log_mul hi.1.1.ne' ha.ne', Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hi.1.1.ne']
  norm_num
  ring

lemma ar_upper {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrSmallSBridgeAR p.s p.k p.chi ≤ Real.log (1 + (1 - p.s) * p.k) := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have hu : 0 ≤ (1 - p.s) * p.k := mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le
  have hlog := Real.log_le_log
    (by nlinarith [mul_nonneg hu hi.2.2.1.le] : 0 < 1 + (1 - p.s) * p.k * p.chi)
    (by nlinarith [mul_le_mul_of_nonneg_left hi.2.2.2.le hu] :
      1 + (1 - p.s) * p.k * p.chi ≤ 1 + (1 - p.s) * p.k)
  have hscaled := mul_le_mul_of_nonneg_left hlog hi.2.2.1.le
  unfold lrSmallSBridgeAR
  rw [div_le_iff₀ (by linarith [hi.2.2.1] : 0 < 1 + p.chi)]
  nlinarith

lemma frozen_lower_basic {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    p.k * (1 + p.chi) / 4 *
        (lrCertificateD p * (1 - p.s) - lrCertificateBFlow p * (p.s + 2 / 7)) +
        (lrCertificateBFlow p - lrCertificateD p) / 4 ≤ frozen p := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have hD : 0 ≤ lrCertificateD p := (lrDeterminantD1_nonnegative hi).trans (lrDeterminantD1_le_D hi)
  have hB := (lrCertificateBFlow_pos hi).le
  have hAR := ar_upper hi
  have hb := b_formula hi
  have hd := d_formula hi
  have hv := lrCertificateV_mem_Ioo hi
  have hbeta : Real.log (1 + lrCertificateV p) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])
  have hq := lrSmallSBridgeQChi_lower ⟨hi.2.2.1.le, hi.2.2.2.le⟩
  have hP : 2 * lrCertificateBFlow p + 1 - p.s ≤ lrLowRatioP p := by
    unfold lrLowRatioP lrSmallSBridgeP
    linarith
  have hS : -2 * lrCertificateD p - p.s - 2 / 7 ≤ lrLowRatioP p - lrLowRatioG p := by
    unfold lrLowRatioP lrLowRatioG lrSmallSBridgeP lrSmallSBridgeG
    linarith
  have h1 := mul_le_mul_of_nonneg_left hP hD
  have h2 := mul_le_mul_of_nonneg_left hS hB
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (div_nonneg (mul_nonneg hk.le (by linarith [hi.2.2.1])) (by norm_num) :
      0 ≤ p.k * (1 + p.chi) / 4)
  unfold frozen
  nlinarith

lemma b_sub_d_lower_small_k {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hsk : p.s ≤ p.k) (hk : p.k ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ lrCertificateBFlow p - lrCertificateD p := by
  have hk0 : 0 < p.k := hi.1.1.trans_le hsk
  have he : lrCertificateE p ≤ 1 / 40 := by
    have h := mul_le_mul_of_nonneg_left hk hi.1.1.le
    change p.s * p.k ≤ 1 / 40
    nlinarith
  have hv := lrCertificateV_mem_Ioo hi
  have hvLo : (7 / 8 : ℝ) ≤ lrCertificateV p := by
    have h := lrLowRatio_one_sub_v_le_e hi
    linarith
  have hbeta : (3 / 5 : ℝ) ≤ Real.log (1 + lrCertificateV p) := by
    have h := lr_log_one_add_lower hv.1.le
    have hlow : (3 / 5 : ℝ) ≤ 2 * lrCertificateV p / (2 + lrCertificateV p) := by
      rw [le_div_iff₀ (by linarith [hv.1] : 0 < 2 + lrCertificateV p)]
      linarith
    exact hlow.trans h
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hk0 hi.1.1)
  rw [inv_div] at hlog
  have hfrac : 4 * (p.k - p.s) ≤ 1 - p.s / p.k := by
    rw [le_sub_iff_add_le]
    apply (le_of_mul_le_mul_right ?_ hk0)
    rw [add_mul, div_mul_cancel₀ _ hk0.ne']
    have h := mul_nonneg (sub_nonneg.mpr hsk) (show 0 ≤ 1 - 4 * p.k by linarith)
    nlinarith
  have ha0 : 0 < 1 + (1 - p.s) * p.k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk0.le]
  have ha := Real.log_le_sub_one_of_pos ha0
  have hak : Real.log (1 + (1 - p.s) * p.k) ≤ p.k := by
    nlinarith [mul_nonneg hi.1.1.le hk0.le]
  have hlogEq : Real.log (p.k / p.s) = Real.log p.k + lrLowRatioLogScale p := by
    unfold lrLowRatioLogScale
    rw [Real.log_div hk0.ne' hi.1.1.ne', Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hi.1.1.ne']
    norm_num
    ring
  rw [hlogEq] at hlog
  rw [b_formula hi, d_formula hi]
  linarith

theorem frozen_small_k {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hsk : p.s ≤ p.k) (hk : p.k ≤ 1 / 4) :
    (1 / 10 : ℝ) < frozen p := by
  let m := p.k * (1 + p.chi)
  let D := lrCertificateD p
  let B := lrCertificateBFlow p
  have hk0 : 0 < p.k := hi.1.1.trans_le hsk
  have hm0 : 0 ≤ m := mul_nonneg hk0.le (by linarith [hi.2.2.1])
  have hm : m ≤ (1 / 2 : ℝ) := by
    have h := mul_le_mul hk (show 1 + p.chi ≤ 2 by linarith [hi.2.2.2])
      (by linarith [hi.2.2.1] : 0 ≤ 1 + p.chi) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    dsimp [m]
    linarith
  have hD : 0 ≤ D := (lrDeterminantD1_nonnegative hi).trans (lrDeterminantD1_le_D hi)
  have hBD : (1 / 2 : ℝ) ≤ B - D := b_sub_d_lower_small_k hi hs hsk hk
  have hcoef : (113 / 140 : ℝ) ≤ 1 - m * (p.s + 2 / 7) := by
    have h := mul_le_mul hm (show p.s + 2 / 7 ≤ 27 / 70 by linarith)
      (show 0 ≤ p.s + 2 / 7 by linarith [hi.1.1]) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hgood := mul_nonneg (mul_nonneg hm0 hD)
    (show 0 ≤ 1 - 2 * p.s - 2 / 7 by linarith)
  have hprod := mul_le_mul hBD hcoef (by norm_num : (0 : ℝ) ≤ 113 / 140)
    (show 0 ≤ B - D by linarith)
  have hlow := frozen_lower_basic hi
  change m / 4 * (D * (1 - p.s) - B * (p.s + 2 / 7)) + (B - D) / 4 ≤ frozen p at hlow
  nlinarith

/-- The entire small-k midpoint face is analytic through s=1/10. -/
theorem midpoint_small_k {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 1 / 4) :
    0 ≤ lrCertificateUTarget p := by
  by_cases hsk : p.s ≤ p.k
  · exact midpoint_of_frozen hi hr hs (hk.trans (by norm_num)) (frozen_small_k hi hs hsk hk).le
  · have hkLo := lrCertificate_k_gt_quarter_s_of_relevant hi hr
    exact LRLowRatioDirectV.midpoint_nonnegative hi hr ⟨hkLo, (lt_of_not_ge hsk).le⟩ hs

end CourtadeKumar.LRAnalyticMidpoint
