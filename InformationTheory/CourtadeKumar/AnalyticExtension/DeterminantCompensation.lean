import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantGap

/-! Convert the entropy, slope and gap bounds into the determinant correction. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

noncomputable def gapFactor (s k C a : ℝ) : ℝ :=
  (1 - 2 * s * C / 7) * (1 - s) / (3 * (C + 15 / 4)) *
    (C + 1 - (1 + (1 - s) * k) * a / ((1 - s) * k))

/-- Cancel the repeated logarithmic scale before interval evaluation. -/
noncomputable def gapFactorH (s C h : ℝ) : ℝ :=
  (1 - 2 * s * C / 7) * (1 - s) / 3 * (1 - (h + 11 / 4) / (C + 15 / 4))

lemma w_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) :
    1 - 2 * p.s * Real.log (4 / p.s) / 7 ≤ 4 * lrCertificateW p / p.s := by
  have h := LRAnalyticMidpoint.omega_zero_lower ⟨hi.1.1, hs⟩
  rw [le_div_iff₀ hi.1.1, lrCertificateW_eq_smallSBridge_split,
    lrLowerFaceOmegaQ0_zero hi.1.1]
  nlinarith

theorem compensation_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    gapFactor p.s p.k (Real.log (4 / p.s)) (Real.log (1 + (1 - p.s) * p.k)) ≤
      lrDeterminantC0 p * lrDeterminantT p / lrLowRatioNormalization p := by
  let C := Real.log (4 / p.s)
  let H := lrDeterminantHd p
  let N := lrLowRatioNormalization p
  let R := 1 - p.s
  let f := 1 - 2 * p.s * C / 7
  let T := C + 1 - lrLowKIdealH (1 + (1 - p.s) * p.k)
  have hC : (7 / 2 : ℝ) ≤ C := LRAnalyticMidpoint.log_four_div_ge ⟨hi.1.1, hs⟩
  have hT : 0 ≤ T := by dsimp [T]; linarith [finite_h_upper hi hk]
  have hR : 0 < R := sub_pos.mpr hi.1.2
  have hN : 0 < N := lrLowRatioNormalization_pos hi
  have hH : 0 < H := lrDeterminantHd_pos hi
  have hHup : H ≤ C + 15 / 4 := hd_upper hi hs hk
  have hf : 0 ≤ f := by
    have h := s_log_upper ⟨hi.1.1, hs⟩
    dsimp [f, C]
    linarith
  have hW : 0 ≤ 4 * lrCertificateW p / p.s := by
    exact div_nonneg (mul_nonneg (by norm_num) (lrCertificateW_pos hi).le) hi.1.1.le
  have hw : f ≤ 4 * lrCertificateW p / p.s := w_lower hi hs
  have hgap : R * T ≤ lrCertificateGap p / N := by
    rw [le_div_iff₀ hN]
    have h := gap_lower hi hs hk
    change R * N * T ≤ lrCertificateGap p at h
    nlinarith
  have hRT : 0 ≤ R * T := mul_nonneg hR.le hT
  have hm := mul_le_mul hw hgap hRT hW
  have hden : 0 < 3 * H := by positivity
  have hdenOrder : 3 * H ≤ 3 * (C + 15 / 4) := by linarith
  have h1 := div_le_div_of_nonneg_left (mul_nonneg hf hRT) hden hdenOrder
  have h2 := div_le_div_of_nonneg_right hm hden.le
  have hk0 : 0 < p.k := lrBoundedDeep_k_pos hi
  have hA : 0 < (1 - p.s) * p.k := mul_pos hR hk0
  have hid : gapFactor p.s p.k C (Real.log (1 + (1 - p.s) * p.k)) =
      f * (R * T) / (3 * (C + 15 / 4)) := by
    unfold gapFactor
    dsimp [f, R, T]
    unfold lrLowKIdealH
    rw [if_neg (by linarith : 1 + (1 - p.s) * p.k ≠ 1)]
    simp only [add_sub_cancel_left]
    ring
  have hid2 : ((4 * lrCertificateW p / p.s) * (lrCertificateGap p / N)) / (3 * H) =
      lrDeterminantC0 p * lrDeterminantT p / N := by
    unfold lrDeterminantC0 lrDeterminantT
    change _ = (4 * R * lrCertificateW p / (3 * p.s * H)) * (lrCertificateGap p / R) / N
    field_simp [hi.1.1.ne', hR.ne', hH.ne', hN.ne']
  change gapFactor p.s p.k C (Real.log (1 + (1 - p.s) * p.k)) ≤ _
  rw [hid]
  exact (h1.trans h2).trans_eq hid2

theorem compensation_lower_h {p : CertificatePoint} {h : ℝ}
    (hi : LRHighShapeInterior p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4)
    (hh : lrLowKIdealH (1 + (1 - p.s) * p.k) ≤ h) :
    gapFactorH p.s (Real.log (4 / p.s)) h ≤
      lrDeterminantC0 p * lrDeterminantT p / lrLowRatioNormalization p := by
  let C := Real.log (4 / p.s)
  let A := (1 - p.s) * p.k
  have hC : (7 / 2 : ℝ) ≤ C := LRAnalyticMidpoint.log_four_div_ge ⟨hi.1.1, hs⟩
  have hden : 0 < C + 15 / 4 := by linarith
  have hf : 0 ≤ 1 - 2 * p.s * C / 7 := by
    have hsl := s_log_upper ⟨hi.1.1, hs⟩
    dsimp [C]
    linarith
  have hcoef : 0 ≤ (1 - 2 * p.s * C / 7) * (1 - p.s) / 3 :=
    div_nonneg (mul_nonneg hf (sub_nonneg.mpr hi.1.2.le)) (by norm_num)
  have hquot := div_le_div_of_nonneg_right (add_le_add_right hh (11 / 4)) hden.le
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hquot 1) hcoef
  have hA : 0 < A := mul_pos (sub_pos.mpr hi.1.2) (lrBoundedDeep_k_pos hi)
  have heq : gapFactorH p.s C (lrLowKIdealH (1 + A)) =
      gapFactor p.s p.k C (Real.log (1 + A)) := by
    unfold gapFactorH gapFactor lrLowKIdealH
    rw [if_neg (by linarith : 1 + A ≠ 1)]
    simp only [add_sub_cancel_left]
    change (1 - 2 * p.s * C / 7) * (1 - p.s) / 3 *
      (1 - ((1 + A) * Real.log (1 + A) / A + 11 / 4) / (C + 15 / 4)) =
      (1 - 2 * p.s * C / 7) * (1 - p.s) / (3 * (C + 15 / 4)) *
      (C + 1 - (1 + A) * Real.log (1 + A) / A)
    field_simp [hA.ne', hden.ne']
    ring
  have hlow : gapFactorH p.s C h ≤ gapFactorH p.s C (lrLowKIdealH (1 + A)) := by
    simpa only [gapFactorH, A, add_comm] using hm
  rw [heq] at hlow
  exact hlow.trans (compensation_lower hi hs hk)

end CourtadeKumar.LRAnalyticDeterminant
