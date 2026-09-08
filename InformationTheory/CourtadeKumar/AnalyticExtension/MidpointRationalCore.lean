import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalBounds
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointCore

/-! The midpoint logarithmic core has a rational lower envelope with just
one interval for B-D and one scalar entropy payment. -/
namespace CourtadeKumar.LRAnalyticMidpoint

noncomputable def alpha (p : CertificatePoint) : ℝ :=
  p.chi / (1 + p.chi) *
    (Real.log (1 + (1 - p.s) * p.k) - Real.log (1 + (1 - p.s) * p.k * p.chi))

noncomputable def loss (p : CertificatePoint) : ℝ :=
  -alpha p - lrSmallSBridgeQChi p.chi

noncomputable def rationalH (s k c : ℝ) : ℝ :=
  1 - k * (1 + c) * s - k * rationalT s k c

noncomputable def rationalU (s k c : ℝ) : ℝ :=
  1 - 2 * s + s * k * (1 - c) / 2 + rationalAlpha s k c - rationalT s k c / (1 + c)

noncomputable def rationalLower (s k c bd payment : ℝ) : ℝ :=
  bd * rationalH s k c + k * (1 + c) * rationalD s k * rationalU s k c - payment

lemma alpha_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    rationalAlpha p.s p.k p.chi ≤ alpha p := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  exact weighted_log_ratio_lower
    (mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le) ⟨hi.2.2.1, hi.2.2.2.le⟩

lemma loss_upper {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    loss p ≤ rationalT p.s p.k p.chi / (1 + p.chi) := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have hA := mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le
  have ha : 0 < 1 + (1 - p.s) * p.k := by linarith
  have hb : 0 < 1 + (1 - p.s) * p.k * p.chi := by
    nlinarith [mul_nonneg hA hi.2.2.1.le]
  have hc : 0 < 1 + p.chi := by linarith [hi.2.2.1]
  have h := weighted_log_ratio_upper hA ⟨hi.2.2.1, hi.2.2.2.le⟩
  rw [Real.log_div hb.ne' (mul_pos hi.2.2.1 ha).ne', Real.log_mul hi.2.2.1.ne' ha.ne'] at h
  have hid : (1 + p.chi) * loss p = p.chi *
      (Real.log (1 + (1 - p.s) * p.k * p.chi) -
        (Real.log p.chi + Real.log (1 + (1 - p.s) * p.k))) := by
    unfold loss alpha lrSmallSBridgeQChi
    field_simp [hc.ne']
    ring
  rw [le_div_iff₀ hc]
  unfold rationalT
  nlinarith [hid]

lemma ar_alpha {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrSmallSBridgeAR p.s p.k p.chi = Real.log (1 + (1 - p.s) * p.k) - alpha p := by
  unfold lrSmallSBridgeAR alpha
  field_simp [show 1 + p.chi ≠ 0 by linarith [hi.2.2.1]]
  ring

lemma p_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioP p = 2 * lrCertificateBFlow p + 1 - p.s +
      2 * (Real.log 2 - Real.log (1 + lrCertificateV p)) + alpha p := by
  unfold lrLowRatioP lrSmallSBridgeP
  rw [ar_alpha hi, b_formula hi]
  ring

lemma s_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrLowRatioP p - lrLowRatioG p = -2 * lrCertificateD p - p.s - loss p := by
  unfold lrLowRatioP lrLowRatioG lrSmallSBridgeP lrSmallSBridgeG loss
  rw [ar_alpha hi, d_formula hi]
  ring

lemma core_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    4 * coreTarget p =
      (lrCertificateBFlow p - lrCertificateD p) *
        (1 - p.k * (1 + p.chi) * p.s - p.k * (1 + p.chi) * loss p) +
      p.k * (1 + p.chi) * lrCertificateD p *
        (1 - 2 * p.s + 2 * (Real.log 2 - Real.log (1 + lrCertificateV p)) + alpha p - loss p) -
      4 * entropyPayment p := by
  unfold coreTarget frozen
  rw [s_identity hi, p_identity hi]
  ring

lemma rationalU_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    rationalU p.s p.k p.chi ≤
      1 - 2 * p.s + 2 * (Real.log 2 - Real.log (1 + lrCertificateV p)) + alpha p - loss p := by
  have ha := alpha_lower hi
  have hl := loss_upper hi
  have hb := beta_gap_lower hi
  unfold rationalU
  linarith

lemma rationalH_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    rationalH p.s p.k p.chi ≤
      1 - p.k * (1 + p.chi) * p.s - p.k * (1 + p.chi) * loss p := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have hc : 0 < 1 + p.chi := by linarith [hi.2.2.1]
  have h := mul_le_mul_of_nonneg_left (loss_upper hi) (mul_nonneg hk.le hc.le)
  have hid : p.k * (1 + p.chi) * (rationalT p.s p.k p.chi / (1 + p.chi)) =
      p.k * rationalT p.s p.k p.chi := by field_simp [hc.ne']
  rw [hid] at h
  unfold rationalH
  linarith

/-- Every remaining transcendental estimate is supplied by a B-D enclosure
and an upper bound for the single entropy payment. -/
theorem rationalLower_le_core {p : CertificatePoint} {payment : ℝ}
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p)
    (hu : 0 ≤ rationalU p.s p.k p.chi) (hpay : 4 * entropyPayment p ≤ payment) :
    rationalLower p.s p.k p.chi (lrCertificateBFlow p - lrCertificateD p) payment ≤
      4 * coreTarget p := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have hm : 0 ≤ p.k * (1 + p.chi) := mul_nonneg hk.le (by linarith [hi.2.2.1])
  have hB := (lrCertificateBFlow_pos hi).le
  have hD : 0 ≤ lrCertificateD p := (lrDeterminantD1_nonnegative hi).trans (lrDeterminantD1_le_D hi)
  have hx : lrCertificateX p ≤ 1 := sub_le_self _ (mul_nonneg hi.2.2.1.le hi.2.1.1.le)
  have hBD : 0 ≤ lrCertificateBFlow p - lrCertificateD p := by
    have h := hr.2
    unfold lrCertificateJ at h
    nlinarith [mul_le_mul_of_nonneg_left hx hB]
  have h1 := mul_le_mul_of_nonneg_left (rationalH_lower hi) hBD
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rationalD_lower hi) hm) hu
  have h3 := mul_le_mul_of_nonneg_left (rationalU_lower hi) (mul_nonneg hm hD)
  rw [core_identity hi]
  unfold rationalLower
  linarith

end CourtadeKumar.LRAnalyticMidpoint
