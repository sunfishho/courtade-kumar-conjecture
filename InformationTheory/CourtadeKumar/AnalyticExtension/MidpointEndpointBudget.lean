import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointSmallK
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointCore

/-! Endpoint bounds for the two quantities left outside the rational
midpoint envelope: B-D and a single scalar entropy payment. -/
open Set
namespace CourtadeKumar.LRAnalyticMidpoint

lemma log_four_div_ge {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    (7 / 2 : ℝ) ≤ Real.log (4 / s) := by
  have h40 : Real.log (40 : ℝ) = 5 * Real.log 2 + Real.log (1 + (1 / 4 : ℝ)) := by
    rw [show (40 : ℝ) = 2 ^ 5 * (1 + 1 / 4) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ 5 ≠ 0) (by norm_num), Real.log_pow]
    norm_num
  have h := lr_log_one_add_lower (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have harg : (40 : ℝ) ≤ 4 / s := by rw [le_div_iff₀ hs.1]; linarith [hs.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 40) harg
  rw [h40] at hlog
  nlinarith [Real.log_two_gt_d9]

noncomputable def entropyWeight (a s : ℝ) : ℝ :=
  s * Real.log (4 / s) * (Real.log (4 / s) - a)

lemma entropyWeight_deriv (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (entropyWeight a)
      ((Real.log (4 / s)) ^ 2 - (2 + a) * Real.log (4 / s) + a) s := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log (4 / s)) (-1 / s) s := by
    have h := ((hasDerivAt_const s (4 : ℝ)).div (hasDerivAt_id s) hs.ne').log
      (div_ne_zero (by norm_num) hs.ne')
    convert h using 1 <;> simp only [id_eq, Pi.div_apply] <;> field_simp [hs.ne'] <;> ring
  have h := ((hasDerivAt_id s).mul hlog).mul (hlog.sub_const a)
  convert h using 1 <;> dsimp [entropyWeight] <;> field_simp [hs.ne'] <;> ring

lemma entropyWeight_mono {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 2) :
    MonotoneOn (entropyWeight a) (Ioc (0 : ℝ) (1 / 10)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) (1 / 10))
  · intro y hy
    exact (entropyWeight_deriv a hy.1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (entropyWeight_deriv a hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    rw [(entropyWeight_deriv a hy.1).deriv]
    have hC := log_four_div_ge ⟨hy.1, hy.2.le⟩
    have h1 := mul_nonneg (sub_nonneg.mpr hC)
      (show 0 ≤ Real.log (4 / y) - 1 / 2 by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr ha.2)
      (show 0 ≤ Real.log (4 / y) - 1 by linarith)
    nlinarith

theorem endpoint_payment {p : CertificatePoint} {sh a C : ℝ}
    (hi : LRHighShapeInterior p) (hss : p.s ≤ sh) (hsh : sh ≤ 1 / 10)
    (ha : a ∈ Icc (0 : ℝ) 2)
    (haLo : a ≤ Real.log (1 + (1 - p.s) * p.k))
    (hC : Real.log (4 / sh) ≤ C) :
    4 * entropyPayment p ≤ (5 / 21 : ℝ) * sh * C * (C - a) := by
  have hs : p.s ∈ Ioc (0 : ℝ) (1 / 10) := ⟨hi.1.1, hss.trans hsh⟩
  have hsh0 : 0 < sh := hi.1.1.trans_le hss
  have hCp := log_four_div_ge hs
  have hCe := log_four_div_ge ⟨hsh0, hsh⟩
  have hB : lrCertificateBFlow p ≤ (Real.log (4 / p.s) - a) / 2 := by
    have hv := lrCertificateV_mem_Ioo hi
    have hbeta := Real.log_le_log (by linarith [hv.1] : 0 < 1 + lrCertificateV p)
      (by linarith [hv.2] : 1 + lrCertificateV p ≤ 2)
    rw [b_formula hi, lrLowRatio_log_four_div_split hi.1.1]
    unfold lrLowRatioLogScale
    linarith
  have hBscaled := mul_le_mul_of_nonneg_right hB
    (mul_nonneg hi.1.1.le (by linarith : 0 ≤ Real.log (4 / p.s)))
  have hmono := entropyWeight_mono ha hs ⟨hsh0, hsh⟩ hss
  have hproduct := mul_le_mul hC (sub_le_sub_right hC a)
    (by linarith [ha.2] : 0 ≤ Real.log (4 / sh) - a) (by linarith : 0 ≤ C)
  have hproductS := mul_le_mul_of_nonneg_left hproduct hsh0.le
  unfold entropyPayment entropyWeight at *
  nlinarith

lemma bd_formula {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrCertificateBFlow p - lrCertificateD p = Real.log (p.k / p.s) / 2 +
      Real.log (1 + lrCertificateV p) - Real.log (1 + (1 - p.s) * p.k) := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  rw [b_formula hi, d_formula hi, Real.log_div hk.ne' hi.1.1.ne']
  unfold lrLowRatioLogScale
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hi.1.1.ne']
  norm_num
  ring

lemma beta_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    (6 / 11 : ℝ) ≤ Real.log (1 + lrCertificateV p) := by
  have hv := lrCertificateV_mem_Ioo hi
  have hvLo := v_lower hi hs hk
  have h := lr_log_one_add_lower hv.1.le
  have hr : (6 / 11 : ℝ) ≤ 2 * lrCertificateV p / (2 + lrCertificateV p) := by
    rw [le_div_iff₀ (by linarith [hv.1] : 0 < 2 + lrCertificateV p)]
    linarith
  exact hr.trans h

theorem endpoint_bd {p : CertificatePoint} {rLo rHi aLo aHi : ℝ}
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4)
    (hrLo : rLo ≤ Real.log (p.k / p.s)) (hrHi : Real.log (p.k / p.s) ≤ rHi)
    (haLo : aLo ≤ Real.log (1 + (1 - p.s) * p.k))
    (haHi : Real.log (1 + (1 - p.s) * p.k) ≤ aHi) :
    max 0 (rLo / 2 + 6 / 11 - aHi) ≤ lrCertificateBFlow p - lrCertificateD p ∧
      lrCertificateBFlow p - lrCertificateD p ≤ rHi / 2 + 7 / 10 - aLo := by
  have hbetaLo := beta_lower hi hs hk
  have hv := lrCertificateV_mem_Ioo hi
  have hbetaHi := (Real.log_le_log (by linarith [hv.1] : 0 < 1 + lrCertificateV p)
    (by linarith [hv.2] : 1 + lrCertificateV p ≤ 2)).trans
    (Real.log_two_lt_d9.le.trans (by norm_num : (0.6931471808 : ℝ) ≤ 7 / 10))
  have hbd := bd_formula hi
  have hB := (lrCertificateBFlow_pos hi).le
  have hx : lrCertificateX p ≤ 1 := sub_le_self _ (mul_nonneg hi.2.2.1.le hi.2.1.1.le)
  have hJ := hr.2
  unfold lrCertificateJ at hJ
  have hbd0 : 0 ≤ lrCertificateBFlow p - lrCertificateD p := by
    nlinarith [mul_le_mul_of_nonneg_left hx hB]
  exact ⟨max_le hbd0 (by linarith), by linarith⟩

end CourtadeKumar.LRAnalyticMidpoint
