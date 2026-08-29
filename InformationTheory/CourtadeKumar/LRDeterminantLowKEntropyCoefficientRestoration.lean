import InformationTheory.CourtadeKumar.LRDeterminantLowKDeltaTUpper
import InformationTheory.CourtadeKumar.LRDeterminantLowKDirectRemainderRestoration

/-!
# Completed entropy/coefficient restoration on the determinant low-`k` row

This module proves the exact change from the true logarithmic channel
coefficient to the determinant coefficient, pays the resulting entropy term
against the audited endpoint budget, and combines that payment with the
proved channel and direct-remainder stages.

Consequently the analytic low-`k` restoration certificate is unconditional,
and the low-`k` determinant theorem depends only on its separate ideal replay
certificate.
-/

open Set

namespace CourtadeKumar

lemma lrLowHalfSlopeBase_eq_lrDA7ChannelAH
    {v : ℝ} (hv : v ≠ -1) :
    lrLowHalfSlopeBase v = lrDA7ChannelAH v := by
  have hden : 1 + v ≠ 0 := by
    intro h
    have hvEq : v = -1 := by linarith only [h]
    exact hv hvEq
  unfold lrLowHalfSlopeBase lrDA7ChannelAH lrFlowM
  rw [show v / (1 + v) / 2 = v / (2 * (1 + v)) by
    field_simp [hden]]

lemma lrDeterminantHd_eq_lrDA7ChannelH_add_r0
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDeterminantHd point =
      lrDA7ChannelH point +
        4 * lrLowerFaceR0 point.s / point.s := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hsplit := lrLowRatio_log_four_div_split hinterior.1.1
  have hQ : lrCertificateQ point.s =
      lrLowerFaceQ0 point.s + lrLowerFaceR0 point.s := by
    unfold lrLowerFaceR0
    ring
  rw [lrDeterminantHd_eq_continuationTail hinterior, hQ,
    lrLowHalfSlopeBase_eq_lrDA7ChannelAH (by linarith [hv.1])]
  unfold lrLowerFaceQ0
  rw [hsplit]
  unfold lrDA7ChannelH
  field_simp [hinterior.1.1.ne']
  ring

lemma lrCertificateW_normalized_eq_r0
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    4 * lrCertificateW point / point.s =
      1 + 4 * lrLowerFaceR0 point.s / point.s -
        4 * lrLowerFaceR0Prime point.s := by
  rw [lrCertificateW_eq_quarter_add_remainder hinterior.1.1]
  field_simp [hinterior.1.1.ne']

theorem lrDA7_channel_c0q_sub_c0_exact
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7ChannelC0Q point - lrDeterminantC0 point =
      (4 * lrDA7ChannelC0Q point / lrDeterminantHd point) *
        (lrDA7ChannelH point * lrLowerFaceR0Prime point.s -
          (lrDA7ChannelH point - 1) *
            (lrLowerFaceR0 point.s / point.s)) := by
  let H := lrDA7ChannelH point
  let Hd := lrDeterminantHd point
  let R := lrCertificateR point
  let r := lrLowerFaceR0 point.s
  let rp := lrLowerFaceR0Prime point.s
  have hH : 0 < H := by
    have hL : 0 < Real.log (1 / point.s) := by
      apply Real.log_pos
      rw [lt_div_iff₀ hinterior.1.1]
      simpa using hinterior.1.2
    exact hL.trans_le (by simpa [H] using lrDA7_channel_H_ge_log_scale hinterior)
  have hHd : 0 < Hd := by
    simpa [Hd] using lrDeterminantHd_pos hinterior
  have hs := hinterior.1.1
  have hHdForm : Hd = H + 4 * r / point.s := by
    simpa [Hd, H, r] using lrDeterminantHd_eq_lrDA7ChannelH_add_r0 hinterior
  have hWForm : lrCertificateW point =
      point.s / 4 + r - point.s * rp := by
    simpa [r, rp] using
      lrCertificateW_eq_quarter_add_remainder (point := point) hs
  have hden : 0 < H + 4 * r / point.s := by
    rw [← hHdForm]
    exact hHd
  have hdenCleared : 0 < H * point.s + 4 * r := by
    calc
      0 < (H + 4 * r / point.s) * point.s := mul_pos hden hs
      _ = H * point.s + 4 * r := by
        field_simp [hs.ne']
  change R / (3 * H) - 4 * R * lrCertificateW point /
        (3 * point.s * Hd) =
      (4 * (R / (3 * H)) / Hd) *
        (H * rp - (H - 1) * (r / point.s))
  rw [hWForm, hHdForm]
  field_simp [hs.ne', hH.ne', hden.ne', hdenCleared.ne']
  ring

lemma lrDA7_channel_c0q_sub_c0_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    0 ≤ lrDA7ChannelC0Q point - lrDeterminantC0 point ∧
      lrDA7ChannelC0Q point - lrDeterminantC0 point ≤
        4 * lrLowerFaceR0Prime point.s * lrDA7ChannelC0Q point := by
  let H := lrDA7ChannelH point
  let Hd := lrDeterminantHd point
  let r := lrLowerFaceR0 point.s
  let rp := lrLowerFaceR0Prime point.s
  let cq := lrDA7ChannelC0Q point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hL := lrDA7_log_scale_pos hsIoc
  have hHLower : Real.log (1 / point.s) ≤ H := by
    simpa [H] using lrDA7_channel_H_ge_log_scale hinterior
  have hH : 1 ≤ H := by
    have hLBase := lrLowK_log_scale_ge_L0 hinterior hregion.1
    have hlogTwo := Real.log_two_gt_d9
    dsimp [lrLowKIdealL0] at hLBase
    nlinarith
  have hHPos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hHdPos : 0 < Hd := by simpa [Hd] using lrDeterminantHd_pos hinterior
  have hHdForm : Hd = H + 4 * r / point.s := by
    simpa [Hd, H, r] using lrDeterminantHd_eq_lrDA7ChannelH_add_r0 hinterior
  have hr0 : 0 ≤ r := by
    simpa [r] using lrLowerFaceR0_nonneg hinterior.1
  have hrp0 : 0 ≤ rp := by
    simpa [rp] using lrLowerFaceR0Prime_nonneg hinterior.1
  have hrSlope : r ≤ point.s * rp := by
    have hWUpper := lrCertificateW_le_quarter hinterior
    rw [lrCertificateW_eq_quarter_add_remainder hinterior.1.1] at hWUpper
    simpa [r, rp] using (show lrLowerFaceR0 point.s ≤
      point.s * lrLowerFaceR0Prime point.s by linarith)
  have hrs : r / point.s ≤ rp := by
    rw [div_le_iff₀ hinterior.1.1]
    simpa [r, rp, mul_comm] using hrSlope
  have hcq0 : 0 ≤ cq := by
    dsimp [cq]
    unfold lrDA7ChannelC0Q
    exact div_nonneg
      (by unfold lrCertificateR; linarith [hinterior.1.2])
      (mul_nonneg (by norm_num) hHPos.le)
  have hfactor0 : 0 ≤ 4 * cq / Hd :=
    div_nonneg (mul_nonneg (by norm_num) hcq0) hHdPos.le
  have hbracket0 :
      0 ≤ H * rp - (H - 1) * (r / point.s) := by
    have hrs0 : 0 ≤ r / point.s := div_nonneg hr0 hinterior.1.1.le
    have hdiff : 0 ≤ rp - r / point.s := sub_nonneg.mpr hrs
    have : H * rp - (H - 1) * (r / point.s) =
        H * (rp - r / point.s) + r / point.s := by ring
    rw [this]
    exact add_nonneg (mul_nonneg hHPos.le hdiff) hrs0
  have hbracketUpper :
      H * rp - (H - 1) * (r / point.s) ≤ H * rp := by
    exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hH)
      (div_nonneg hr0 hinterior.1.1.le))
  have hexact := lrDA7_channel_c0q_sub_c0_exact hinterior
  have hfirst := mul_le_mul_of_nonneg_left hbracketUpper hfactor0
  have hratio : H / Hd ≤ 1 := by
    rw [div_le_one hHdPos]
    rw [hHdForm]
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) hr0) hinterior.1.1.le)
  have hsecond : (4 * cq / Hd) * (H * rp) ≤ 4 * rp * cq := by
    have hscaled := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hcq0) hrp0)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hscaled
  rw [hexact]
  exact ⟨mul_nonneg hfactor0 hbracket0, hfirst.trans hsecond⟩

lemma lrDA7_channel_c0q_sub_c0_pointwise_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelC0Q point - lrDeterminantC0 point ≤
      point.s * (Real.log (1 / point.s) + 7 / 5) /
        (2 * Real.log (1 / point.s)) := by
  let L := Real.log (1 / point.s)
  let H := lrDA7ChannelH point
  let rp := lrLowerFaceR0Prime point.s
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hLPos : 0 < L := by simpa [L] using lrDA7_log_scale_pos hsIoc
  have hHLower : L ≤ H := by
    simpa [L, H] using lrDA7_channel_H_ge_log_scale hinterior
  have hHPos : 0 < H := hLPos.trans_le hHLower
  have hcq : lrDA7ChannelC0Q point ≤ 1 / (3 * H) := by
    have hR : lrCertificateR point ≤ 1 := by
      unfold lrCertificateR
      linarith [hinterior.1.1]
    unfold lrDA7ChannelC0Q
    exact div_le_div_of_nonneg_right hR
      (mul_nonneg (by norm_num) hHPos.le)
  have hrp0 : 0 ≤ rp := by
    simpa [rp] using lrLowerFaceR0Prime_nonneg hinterior.1
  have hcoeff := (lrDA7_channel_c0q_sub_c0_bounds hinterior hregion).2
  have hcoeff' : lrDA7ChannelC0Q point - lrDeterminantC0 point ≤
      4 * rp / (3 * H) := by
    have hscaled := mul_le_mul_of_nonneg_left hcq
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hrp0)
    calc
      lrDA7ChannelC0Q point - lrDeterminantC0 point ≤
          4 * lrLowerFaceR0Prime point.s * lrDA7ChannelC0Q point := hcoeff
      _ ≤ 4 * rp / (3 * H) := by
        simpa [rp, H, div_eq_mul_inv, mul_assoc] using hscaled
  have hs16 : point.s ∈ Ioo (0 : ℝ) (1 / 16) :=
    ⟨hinterior.1.1, hregion.1.trans_lt (by norm_num)⟩
  have hrpRaw := lrLowerFaceR0Prime_upper hs16
  have hlogSplit := lrLowRatio_log_four_div_split hinterior.1.1
  have hrp : rp ≤ point.s / 3 * (L + 7 / 5) := by
    have hlogTwo : 2 * Real.log 2 ≤ (7 / 5 : ℝ) := by
      nlinarith [Real.log_two_lt_d9]
    have hscale0 : 0 ≤ point.s / 3 :=
      div_nonneg hinterior.1.1.le (by norm_num)
    have hlogBound := mul_le_mul_of_nonneg_left
      (add_le_add_left hlogTwo L) hscale0
    rw [hlogSplit] at hrpRaw
    have hlogBound' :
        point.s / 3 * (L + 2 * Real.log 2) ≤
          point.s / 3 * (L + 7 / 5) := by
      simpa [add_comm] using hlogBound
    simpa [rp, L] using hrpRaw.trans hlogBound'
  have hnum0 : 0 ≤ point.s * (L + 7 / 5) :=
    mul_nonneg hinterior.1.1.le (add_nonneg hLPos.le (by norm_num))
  have hcross :
      4 * rp * L ≤ (3 / 2 : ℝ) * point.s *
        (L + 7 / 5) * H := by
    have hrpScaled := mul_le_mul_of_nonneg_right hrp
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hLPos.le)
    have hHL := mul_le_mul_of_nonneg_left hHLower hnum0
    nlinarith [hrpScaled, hHL]
  exact hcoeff'.trans (by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hHPos)
      (mul_pos (by norm_num) hLPos)]
    nlinarith [hcross])

/-! ## Endpoint monotonicity for the entropy polynomial -/

noncomputable def lrDA7PEntWeight (s : ℝ) : ℝ :=
  s * lrDA7PEnt (Real.log (1 / s))

lemma hasDerivAt_lrDA7PEntWeight
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt lrDA7PEntWeight
      (lrDA7PEnt (Real.log (1 / s)) -
        lrDA7PEntPrime (Real.log (1 / s))) s := by
  have hL := hasDerivAt_lrDA7Log hs
  have h1 := hL.add_const (7 / 5)
  have h2 := (hL.const_mul (1 / 2)).add_const (7 / 10 + 1 / 256)
  have h3 := hL.add_const (3 / 2)
  have hprod := (hasDerivAt_id s).mul ((h1.mul h2).mul h3)
  unfold lrDA7PEntWeight lrDA7PEnt lrDA7PEntPrime
  convert hprod using 1
  · funext x
    simp only [Pi.mul_apply, id_eq]
    ring
  · simp only [Pi.mul_apply, id_eq]
    field_simp [hs.ne']
    ring

lemma lrDA7PEntWeight_monotoneOn :
    MonotoneOn lrDA7PEntWeight (Ioc (0 : ℝ) lrDA7S0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) lrDA7S0)
  · intro s hs
    exact (hasDerivAt_lrDA7PEntWeight hs.1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact (hasDerivAt_lrDA7PEntWeight hs.1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    rw [(hasDerivAt_lrDA7PEntWeight hs.1).deriv]
    exact (lrDA7_endpoint_polynomial_gaps_pos
      (lrDA7_log_scale_ge_LMinus
        (show s ∈ Ioc (0 : ℝ) lrDA7S0 from ⟨hs.1, hs.2.le⟩))).2.2.le

lemma lrDA7PEnt_endpoint_order :
    lrDA7PEnt (7 * Real.log 2) ≤ lrDA7PEnt lrDA7LPlus := by
  have horder := lrDA7_log_window.2.le
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ 7 * Real.log 2 + 7 / 5 := by positivity
  have hB0 : 0 ≤ 7 * Real.log 2 / 2 + 7 / 10 + 1 / 256 := by positivity
  have hC0 : 0 ≤ 7 * Real.log 2 + 3 / 2 := by positivity
  have hAUpper0 : 0 ≤ lrDA7LPlus + 7 / 5 := by
    norm_num [lrDA7LPlus]
  have hBUpper0 : 0 ≤ lrDA7LPlus / 2 + 7 / 10 + 1 / 256 := by
    norm_num [lrDA7LPlus]
  have hA : 7 * Real.log 2 + 7 / 5 ≤ lrDA7LPlus + 7 / 5 := by
    linarith
  have hB : 7 * Real.log 2 / 2 + 7 / 10 + 1 / 256 ≤
      lrDA7LPlus / 2 + 7 / 10 + 1 / 256 := by
    linarith
  have hC : 7 * Real.log 2 + 3 / 2 ≤ lrDA7LPlus + 3 / 2 := by
    linarith
  unfold lrDA7PEnt
  exact mul_le_mul (mul_le_mul hA hB hB0 hAUpper0) hC hC0
    (mul_nonneg hAUpper0 hBUpper0)

lemma lrDA7_s_mul_PEnt_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    s * lrDA7PEnt (Real.log (1 / s)) ≤
      lrDA7S0 * lrDA7PEnt lrDA7LPlus := by
  have hmono := lrDA7PEntWeight_monotoneOn hs
    (show lrDA7S0 ∈ Ioc (0 : ℝ) lrDA7S0 by norm_num [lrDA7S0]) hs.2
  have hendpointLog : Real.log (1 / lrDA7S0) = 7 * Real.log 2 := by
    dsimp [lrDA7S0]
    rw [show (1 / (1 / 128 : ℝ)) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  unfold lrDA7PEntWeight at hmono
  rw [hendpointLog] at hmono
  have hscaled := mul_le_mul_of_nonneg_left lrDA7PEnt_endpoint_order
    (show 0 ≤ lrDA7S0 by norm_num [lrDA7S0])
  exact hmono.trans hscaled

/-! ## Entropy payment, conditional only on the channel-`T` envelope -/

theorem lrBoundedDeep_entropyCoefficient_of_channelT_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point)
    (hT : lrDA7ChannelT point ≤
      Real.log (1 / point.s) + 3 / 2) :
    lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point ≤
      lrDA7EntropyEndpoint := by
  let L := Real.log (1 / point.s)
  let dc := lrDA7ChannelC0Q point - lrDeterminantC0 point
  let J := lrDA7ChannelJ1 point
  let T := lrDA7ChannelT point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hLPos : 0 < L := by simpa [L] using lrDA7_log_scale_pos hsIoc
  have hLMinus : lrDA7LMinus ≤ L := lrDA7_log_scale_ge_LMinus hsIoc
  have hdcBounds := lrDA7_channel_c0q_sub_c0_bounds hinterior hregion
  have hdc0 : 0 ≤ dc := by simpa [dc] using hdcBounds.1
  have hdc : dc ≤ point.s * (L + 7 / 5) / (2 * L) := by
    simpa [dc, L] using
      lrDA7_channel_c0q_sub_c0_pointwise_upper hinterior hregion
  have hJ0 : 0 ≤ J := by
    dsimp [J, lrDA7ChannelJ1]
    exact (lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant).le
  have hJ : J ≤ L / 2 + 7 / 10 + 1 / 256 := by
    have hraw := lrDA7_channel_j1_le_log_scale_half_add_log_two hinterior
    dsimp [J, L]
    nlinarith [Real.log_two_lt_d9]
  have hTUpper : T ≤ L + 3 / 2 := by simpa [T, L] using hT
  have hJMax0 : 0 ≤ L / 2 + 7 / 10 + 1 / 256 := by positivity
  have hdcMax0 : 0 ≤ point.s * (L + 7 / 5) / (2 * L) :=
    div_nonneg
      (mul_nonneg hinterior.1.1.le (add_nonneg hLPos.le (by norm_num)))
      (mul_nonneg (by norm_num) hLPos.le)
  have hweight := lrDA7_s_mul_PEnt_upper hsIoc
  have hLminusPos : 0 < lrDA7LMinus := by norm_num [lrDA7LMinus]
  have hendpoint : point.s * lrDA7PEnt L / (2 * L) ≤
      lrDA7S0 * lrDA7PEnt lrDA7LPlus / (2 * lrDA7LMinus) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hLPos)
      (mul_pos (by norm_num) hLminusPos)]
    have hweight0 : 0 ≤ lrDA7S0 * lrDA7PEnt lrDA7LPlus := by
      unfold lrDA7PEnt
      norm_num [lrDA7S0, lrDA7LPlus]
    have hcross := mul_le_mul hweight hLMinus hLminusPos.le hweight0
    nlinarith [hcross]
  rw [lrBoundedDeep_trueQ_sub_actualQCoefficient]
  by_cases hT0 : 0 ≤ T
  · have hprod : dc * J * T ≤
        point.s * lrDA7PEnt L / (2 * L) := by
      have h1 := mul_le_mul hdc hJ hJ0 hdcMax0
      have h2 := mul_le_mul h1 hTUpper hT0
        (mul_nonneg hdcMax0 hJMax0)
      calc
        dc * J * T ≤
            point.s * (L + 7 / 5) / (2 * L) *
              (L / 2 + 7 / 10 + 1 / 256) * (L + 3 / 2) := h2
        _ = point.s * lrDA7PEnt L / (2 * L) := by
          unfold lrDA7PEnt
          ring
    dsimp [dc, J, T] at hprod
    calc
      (lrDA7ChannelC0Q point - lrDeterminantC0 point) *
            lrDA7ChannelJ1 point * lrDA7ChannelT point ≤
          point.s * lrDA7PEnt L / (2 * L) := hprod
      _ ≤ lrDA7S0 * lrDA7PEnt lrDA7LPlus /
            (2 * lrDA7LMinus) := hendpoint
      _ = lrDA7EntropyEndpoint := by
        unfold lrDA7EntropyEndpoint lrDA7PEnt
        ring
  · have hprodNonpos : dc * J * T ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hdc0 hJ0)
        (le_of_not_ge hT0)
    have hbudget0 : 0 ≤ lrDA7EntropyEndpoint := by
      norm_num [lrDA7EntropyEndpoint, lrDA7S0, lrDA7LPlus,
        lrDA7LMinus]
    dsimp [dc, J, T] at hprodNonpos
    exact hprodNonpos.trans hbudget0

/-- The low-`k` entropy/coefficient payment after the true channel. -/
theorem lrBoundedDeep_entropyCoefficient_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point ≤
      lrDA7EntropyEndpoint := by
  exact lrBoundedDeep_entropyCoefficient_of_channelT_upper
    hinterior hrelevant hregion
    (lrDA7_channelT_upper_lowK hinterior hregion)

/-- All three post-finite low-`k` restoration stages are now analytic. -/
noncomputable def lrLowKRemainingRestoration_proved
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    LRLowKRemainingRestoration point :=
  lrLowKRemainingRestoration_of_entropyCoefficient
    hinterior hrelevant hregion
    (lrBoundedDeep_entropyCoefficient_lowK hinterior hrelevant hregion)

/-- Unconditional analytic restoration certificate on the low-`k` row. -/
theorem lrLowKRestorationCertificate_proved :
    LRLowKRestorationCertificate := by
  exact lrLowKRestorationCertificate_of_remaining
    (fun point hinterior hrelevant hregion ↦
      lrLowKRemainingRestoration_proved hinterior hrelevant hregion)

/-- The low-`k` determinant theorem now depends only on its ideal replay. -/
theorem lrDeterminantLowKRegion_certificate_of_ideal
    (ideal : LRLowKIdealReplayCertificate) :
    LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion :=
  lrDeterminantLowKRegion_certificate_of_analyticData
    ideal lrLowKRestorationCertificate_proved

end CourtadeKumar
