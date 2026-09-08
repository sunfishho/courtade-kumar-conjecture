import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointEntropy

/-! The full midpoint region reduces to a scalar logarithmic core with
a single uniform entropy payment. No numerical channel restoration remains. -/
open Set
namespace CourtadeKumar.LRAnalyticMidpoint

noncomputable def logSquareWeight (s : ℝ) : ℝ := s * (Real.log (4 / s)) ^ 2

lemma logSquareWeight_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt logSquareWeight
      (Real.log (4 / s) * (Real.log (4 / s) - 2)) s := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log (4 / s)) (-1 / s) s := by
    have h := ((hasDerivAt_const s (4 : ℝ)).div (hasDerivAt_id s) hs.ne').log
      (div_ne_zero (by norm_num) hs.ne')
    convert h using 1 <;> simp only [id_eq, Pi.div_apply] <;> field_simp [hs.ne'] <;> ring
  have h := (hasDerivAt_id s).mul (hlog.pow 2)
  convert h using 1 <;> dsimp [logSquareWeight] <;> field_simp [hs.ne'] <;> ring

lemma logSquareWeight_upper {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    (5 / 84 : ℝ) * logSquareWeight s < 1 / 10 := by
  have hlogEnd : Real.log (4 / (1 / 8 : ℝ)) = 5 * Real.log 2 := by
    rw [show (4 / (1 / 8 : ℝ)) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hmono : MonotoneOn logSquareWeight (Ioc (0 : ℝ) (1 / 8)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) (1 / 8))
    · intro y hy
      exact (logSquareWeight_deriv hy.1).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      exact (logSquareWeight_deriv hy.1).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      rw [(logSquareWeight_deriv hy.1).deriv]
      have harg : (4 / (1 / 8 : ℝ)) ≤ 4 / y :=
        div_le_div_of_nonneg_left (by norm_num) hy.1 hy.2.le
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4 / (1 / 8)) harg
      rw [hlogEnd] at hlog
      have hL : 2 ≤ Real.log (4 / y) := by nlinarith [Real.log_two_gt_d9]
      exact mul_nonneg (by linarith) (by linarith)
  have h := hmono ⟨hs.1, hs.2.trans (by norm_num)⟩
    (show (1 / 8 : ℝ) ∈ Ioc 0 (1 / 8) by norm_num) (hs.2.trans (by norm_num))
  have hend : logSquareWeight (1 / 8) = (1 / 8 : ℝ) * (5 * Real.log 2) ^ 2 := by
    unfold logSquareWeight
    rw [hlogEnd]
  rw [hend] at h
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 < (7 / 10 : ℝ) := Real.log_two_lt_d9.trans (by norm_num)
  have hlSq : (Real.log 2) ^ 2 < (49 / 100 : ℝ) := by nlinarith
  nlinarith

theorem r0_restoration {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    -p.s / 10 <
      lrSmallSBridgeChannelReserve (lrCertificateD p) (lrCertificateBFlow p)
        (lrCertificateV p) (lrCertificateX p) (lrLowerFaceOmegaR0 p.s 0)
        (lrSmallSBridgeR0G p) (lrLowerFacePWR0 p.s p.k p.chi (lrCertificateV p)) := by
  let B := lrCertificateBFlow p
  let C := Real.log (4 / p.s)
  have hB : 0 ≤ B := (lrCertificateBFlow_pos hi).le
  have hBU : B ≤ C / 2 := by
    have h := lrLowRatio_B_upper hi
    dsimp [B, C]
    rw [lrLowRatio_log_four_div_split hi.1.1]
    dsimp [lrLowRatioLogScale] at h
    linarith
  have hC : 0 ≤ C := Real.log_nonneg (by
    rw [one_le_div₀ hi.1.1]
    linarith [hs])
  have hW := omega_zero_lower ⟨hi.1.1, hs⟩
  have hscaled := mul_le_mul_of_nonneg_left hW
    (show 0 ≤ (5 / 3 : ℝ) * B by positivity)
  have hBscaled := mul_le_mul_of_nonneg_right hBU
    (mul_nonneg (sq_nonneg p.s) hC)
  have henv := logSquareWeight_upper ⟨hi.1.1, hs⟩
  have henvScaled := mul_lt_mul_of_pos_left henv hi.1.1
  have hreserve := channel_r0_lower hi hr hs hk
  unfold logSquareWeight at henvScaled
  change (5 / 3 : ℝ) * B * lrLowerFaceOmegaR0 p.s 0 ≤ _ at hreserve
  dsimp [C] at hBscaled
  dsimp [B, C] at hBU hBscaled hscaled hreserve henvScaled
  nlinarith

noncomputable def frozen (p : CertificatePoint) : ℝ :=
  p.k * (1 + p.chi) / 4 *
    (lrCertificateD p * lrLowRatioP p + lrCertificateBFlow p * (lrLowRatioP p - lrLowRatioG p)) +
    (lrCertificateBFlow p - lrCertificateD p) / 4

lemma frozen_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrSmallSBridgeFrozenChannelReserve (lrCertificateD p) (lrCertificateBFlow p)
      (lrLowerFaceOmegaQ0 p.s 0)
      (lrLowerFaceQ0 (lrCertificateY0 p) + lrLowerFaceQ0 (lrCertificateE p))
      (lrLowerFacePWQ0 p.s p.k p.chi 1) = p.s * frozen p := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have hc : p.chi ∈ Icc (0 : ℝ) 1 := ⟨hi.2.2.1.le, hi.2.2.2.le⟩
  have hG := lrLowRatioQ0G_frozen_eq_of_pos hi.1.1 hk hc
  have hP := lrLowRatioPWQ0_frozen_eq_of_physical hi.1 hk hi.2.1.2 hc
  change lrLowerFaceQ0 (lrCertificateY0 p) + lrLowerFaceQ0 (lrCertificateE p) = _ at hG
  rw [hG, hP, lrLowerFaceOmegaQ0_zero hi.1.1]
  unfold lrSmallSBridgeFrozenChannelReserve frozen lrLowRatioP lrLowRatioG lrLowRatioLogScale lrSmallSBridgeS
  ring

/-- The logarithmic scalar core is now the only mathematical midpoint input. -/
theorem numerator_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    p.s * (frozen p - 1 / 10) < lrCertificateHalfMidpointNumerator p := by
  have hq := q0_restoration hi hr hs hk
  rw [frozen_identity hi] at hq
  have hrest := r0_restoration hi hr hs hk
  rw [lrCertificateHalfMidpointNumerator_eq_q0_add_r0
    (by linarith [(lrCertificateV_mem_Ioo hi).1] : lrCertificateV p ≠ -1)]
  linarith

theorem midpoint_of_frozen {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4)
    (hf : (1 / 10 : ℝ) ≤ frozen p) : 0 ≤ lrCertificateUTarget p := by
  have h := numerator_lower hi hr hs hk
  have h0 := mul_nonneg hi.1.1.le (sub_nonneg.mpr hf)
  unfold lrCertificateUTarget lrCertificateUDenominator
  exact div_nonneg (by linarith) (mul_nonneg hi.1.1.le hi.2.1.1.le)

end CourtadeKumar.LRAnalyticMidpoint
