import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantEntropy
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantRadial
import InformationTheory.CourtadeKumar.LRDeterminantLowKDirectRemainderRestoration

/-! A lower bound for the full compensation, retaining the frozen gap. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

lemma h_one_add_upper {a : ℝ} (ha : 0 < a) :
    lrLowKIdealH (1 + a) ≤ 1 + a / 2 := by
  have h := lrIdealH_log_one_add_upper ha.le
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 + a by linarith)
  have hid : (1 + a) * (a - a ^ 2 / (2 * (1 + a))) = a * (1 + a / 2) := by
    field_simp [show 1 + a ≠ 0 by linarith]; ring
  rw [hid] at hm
  unfold lrLowKIdealH
  rw [if_neg (by linarith : 1 + a ≠ 1)]
  simp only [add_sub_cancel_left]
  exact (div_le_iff₀ ha).mpr (by nlinarith)

lemma finite_h_upper {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hk : p.k ≤ 4) :
    lrLowKIdealH (1 + (1 - p.s) * p.k) ≤ 3 := by
  have hk0 : 0 < p.k := lrBoundedDeep_k_pos hi
  have hA : 0 < (1 - p.s) * p.k := mul_pos (sub_pos.mpr hi.1.2) hk0
  have hAu : (1 - p.s) * p.k ≤ 4 := by nlinarith [hi.1.1, hk0, hk]
  exact (h_one_add_upper hA).trans (by linarith)

lemma finite_t_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    Real.log (4 / p.s) + 1 - lrLowKIdealH (1 + (1 - p.s) * p.k) ≤ lrDA7FiniteT p := by
  have hk0 : 0 < p.k := lrBoundedDeep_k_pos hi
  have hA : 0 ≤ (1 - p.s) * p.k := mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk0.le
  have hm := lrLowKIdealH_monotone_Ici
    (show 1 + (1 - p.s) * p.k * p.chi ∈ Ici (1 : ℝ) by
      change 1 ≤ 1 + (1 - p.s) * p.k * p.chi
      nlinarith [mul_nonneg hA hi.2.2.1.le])
    (show 1 + (1 - p.s) * p.k ∈ Ici (1 : ℝ) by
      change 1 ≤ 1 + (1 - p.s) * p.k
      linarith)
    (show 1 + (1 - p.s) * p.k * p.chi ≤ 1 + (1 - p.s) * p.k by
      nlinarith [mul_le_mul_of_nonneg_left hi.2.2.2.le hA])
  have hscaled := mul_le_mul_of_nonneg_left hm hi.2.2.1.le
  have hAH : lrDA7FiniteAH p ≤ lrLowKIdealH (1 + (1 - p.s) * p.k) := by
    unfold lrDA7FiniteAH
    rw [div_le_iff₀ (by linarith [hi.2.2.1] : 0 < 1 + p.chi)]
    nlinarith
  unfold lrDA7FiniteT
  rw [lrLowRatio_log_four_div_split hi.1.1]
  linarith

lemma q_increment_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    (1 - p.s) * lrCertificateE p / 4 ≤
      lrLowerFaceQ0 (lrCertificateB p.s (lrCertificateE p)) - lrLowerFaceQ0 p.s := by
  have h := lrLowerFaceQ0_B_sk_sub hi.1 (lrBoundedDeep_k_pos hi)
  have hT : 1 ≤ Real.log (1 / p.s) + 2 * Real.log 2 + 1 -
      lrLowKIdealH (1 + (1 - p.s) * p.k) := by
    have hC := LRAnalyticMidpoint.log_four_div_ge ⟨hi.1.1, hs⟩
    rw [lrLowRatio_log_four_div_split hi.1.1] at hC
    linarith [finite_h_upper hi hk]
  have hm := mul_le_mul_of_nonneg_left hT
    (show 0 ≤ (1 - p.s) * lrCertificateE p / 4 by
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hi.1.2.le) hi.2.1.1.le) (by norm_num))
  change _ ≤ lrLowerFaceQ0 (lrCertificateB p.s (p.s * p.k)) - lrLowerFaceQ0 p.s
  rw [h]
  unfold lrCertificateE at hm ⊢
  nlinarith

lemma qgap_radial_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrBoundedDeepQGap p = lrBoundedDeepQGapFrozen p +
      (1 - p.s) * lrCertificateG0 (lrCertificateV p) +
      lrLowRatioBWeight p *
        (lrLowerFaceQ0 (lrCertificateB p.s (lrCertificateE p)) - lrLowerFaceQ0 p.s) +
      lrLowRatioKappa p *
        (lrLowerFaceQ0 (lrCertificateB p.s (lrCertificateE p)) - p.s * Real.log 2) := by
  have hv := lrCertificateV_mem_Ioo hi
  simp only [lrBoundedDeepQGap, lrBoundedDeepQGapFrozen, lrBoundedDeepQSquareTarget,
    lrBoundedDeepQPrefixAtM, lrLowRatioKappa, lrLowRatioAWeight, lrLowRatioBWeight]
  field_simp [hv.1.ne', show 1 + lrCertificateV p ≠ 0 by linarith [hv.1]]
  ring

lemma qgap_frozen_le {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrBoundedDeepQGapFrozen p ≤ lrBoundedDeepQGap p := by
  let v := lrCertificateV p
  let d := 1 - v
  let e := lrCertificateE p
  let b := lrLowRatioBWeight p
  have hv := lrCertificateV_mem_Ioo hi
  have hR : 0 ≤ 1 - p.s := sub_nonneg.mpr hi.1.2.le
  have hw := finite_weight_bounds hi hs hk
  have hinc := q_increment_lower hi hs hk
  have hgeom : d * (1 + v) ≤ e := by
    dsimp [d, v, e]
    nlinarith [LRLowRatioAnalyticExtension.one_sub_v_sq_le_e hi]
  have hgood : d ^ 2 / 2 ≤ b * e / 4 := by
    have hb : b = 2 * d / (1 + v) := (lrLowRatio_weight_identities hi).2.1
    have hm := mul_le_mul_of_nonneg_left hgeom (show 0 ≤ d from sub_nonneg.mpr hv.2.le)
    calc
      d ^ 2 / 2 ≤ 2 * d * e / (4 * (1 + v)) := by
        rw [le_div_iff₀ (by linarith [hv.1] : 0 < 4 * (1 + v))]
        nlinarith
      _ = b * e / 4 := by
        rw [hb]
        field_simp [show 1 + v ≠ 0 by linarith [hv.1]]
  have hg := g0_finite_lower ⟨LRAnalyticMidpoint.v_lower hi hs hk, hv.2.le⟩
  have hgR := mul_le_mul_of_nonneg_left hg hR
  have hgoodR := mul_le_mul_of_nonneg_left hgood hR
  have hincB := mul_le_mul_of_nonneg_left hinc hw.1
  have hQs : p.s * Real.log 2 ≤ lrLowerFaceQ0 p.s := by
    have hC := LRAnalyticMidpoint.log_four_div_ge ⟨hi.1.1, hs⟩
    have hm := mul_le_mul_of_nonneg_left hC hi.1.1.le
    have hl := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hi.1.1.le
    unfold lrLowerFaceQ0
    nlinarith [hi.1.1]
  have hQbe : p.s * Real.log 2 ≤ lrLowerFaceQ0 (lrCertificateB p.s e) := by
    have hn := mul_nonneg hR hi.2.1.1.le
    change _ ≤ lrLowerFaceQ0 (lrCertificateB p.s (lrCertificateE p))
    linarith
  have hkap := mul_nonneg hw.2.2.1 (sub_nonneg.mpr hQbe)
  rw [qgap_radial_identity hi]
  dsimp [b, e, d, v] at hgoodR hkap
  nlinarith [mul_nonneg hR (sq_nonneg (1 - lrCertificateV p))]

lemma gap_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    (1 - p.s) * lrLowRatioNormalization p *
      (Real.log (4 / p.s) + 1 - lrLowKIdealH (1 + (1 - p.s) * p.k)) ≤ lrCertificateGap p := by
  have ht := finite_t_lower hi
  have hn := (lrLowRatioNormalization_pos hi).le
  have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg (sub_nonneg.mpr hi.1.2.le) hn)
  have hq := qgap_frozen_le hi hs hk
  rw [lrBoundedDeep_qGap_frozen_eq hi] at hq
  have hr := lrBoundedDeep_RGap_nonnegative_lowK hi
  rw [lrBoundedDeep_gap_eq_q_add_r]
  change (1 - p.s) * lrLowRatioNormalization p * lrDA7FiniteT p ≤ _ at hq
  linarith

end CourtadeKumar.LRAnalyticDeterminant
