import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreAssembly
import InformationTheory.CourtadeKumar.LRDeterminantLowKEntropyCoefficientRestoration
import InformationTheory.CourtadeKumar.LRSmallSBridgeRemainderLoss

/-!
# Restricted bounded-deep restoration endpoints

This module proves the two last stages of the four-stage determinant
restoration telescope on the only deep band needed by the restricted closure:

* `s <= 2^-14`,
* `1 <= k <= 4`, and
* the physical open channel.

The entropy/coefficient stage keeps the exact `c_q-c_0` identity and uses
endpoint monotonicity at `s = 2^-14`.  In particular it does not replace the
logarithmic scale by the much coarser old `LMinus/LPlus` window.  The direct
remainder stage reuses the unconditional sign collector and pays its single
adverse `Omega_r` term with a very coarse bound; the `10^-6` budget has ample
slack on this band.

The final structure records only the genuinely preceding finite and
true-channel stages and assembles them directly with these two proved
endpoints.  It avoids the obsolete ten-field global bounded-deep input record.
-/

open Set

namespace CourtadeKumar

/-! ## Common restricted-band data -/

private lemma lrRestrictedDeep_smallS
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
  ⟨hinterior.1.1, hdeep.1⟩

private lemma lrRestrictedDeep_kBand
    {point : CertificatePoint}
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    point.k ∈ Icc (1 / 4 : ℝ) 4 :=
  ⟨(show (1 / 4 : ℝ) ≤ 1 by norm_num).trans hkOne, hkFour⟩

private lemma lrRestrictedDeep_chiBand
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    point.chi ∈ Icc (0 : ℝ) 1 :=
  ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩

lemma lrRestrictedDeep_e_le_four_s
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hkFour : point.k ≤ 4) :
    lrCertificateE point ≤ 4 * point.s := by
  unfold lrCertificateE
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hkFour hinterior.1.1.le)

lemma lrRestrictedDeep_e_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    0 < lrCertificateE point ∧ lrCertificateE point ≤ 1 / 4096 := by
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hk := lrRestrictedDeep_kBand hkOne hkFour
  simpa [lrCertificateE] using lrSmallSBridgeE_upper hs hk

lemma lrRestrictedDeep_log_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    14 * Real.log 2 ≤ Real.log (1 / point.s) := by
  exact lrSmallSBridge_log_lower (lrRestrictedDeep_smallS hinterior hdeep)

/-! ## Small-channel weights on `1 <= k <= 4` -/

lemma lrDA7_channel_b_bounds_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7ChannelB point ∧
      lrDA7ChannelB point ≤ (501 / 500 : ℝ) * lrCertificateE point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  let d := 1 - v
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hk := lrRestrictedDeep_kBand hkOne hkFour
  have hchi := lrRestrictedDeep_chiBand hinterior
  have hv := lrCertificateV_mem_Ioo hinterior
  have hd : d ≤ (501 / 1000 : ℝ) * e := by
    simpa [d, v, e] using lrSmallSBridge_one_sub_v_le hs hk hchi
  have hd0 : 0 ≤ d := by dsimp [d, v]; linarith [hv.2]
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hbEq : lrDA7ChannelB point = 2 * d / (1 + v) := by
    have hdenNe : 1 + lrCertificateV point ≠ 0 := by
      simpa [v] using hden.ne'
    dsimp [d, v]
    unfold lrDA7ChannelB
    apply (eq_div_iff hdenNe).2
    rw [sub_mul, div_mul_cancel₀ _ hdenNe]
    ring
  rw [hbEq]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hd0) hden.le
  · rw [div_le_iff₀ hden]
    have he0 : 0 ≤ e := by simpa [e] using hinterior.2.1.1.le
    have hscaled := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 1 + v by linarith [hv.1])
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 501 / 500) he0)
    nlinarith

lemma lrDA7_channel_kappa_le_e_sq_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrDA7ChannelKappa point ≤ lrCertificateE point ^ 2 := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  let d := 1 - v
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hk := lrRestrictedDeep_kBand hkOne hkFour
  have hchi := lrRestrictedDeep_chiBand hinterior
  have he := lrRestrictedDeep_e_upper hinterior hdeep hkOne hkFour
  have hv := lrCertificateV_mem_Ioo hinterior
  have hd : d ≤ (501 / 1000 : ℝ) * e := by
    simpa [d, v, e] using lrSmallSBridge_one_sub_v_le hs hk hchi
  have hd0 : 0 ≤ d := by dsimp [d, v]; linarith [hv.2]
  have hvHalf : (1 / 2 : ℝ) ≤ v := by
    dsimp [d] at hd
    nlinarith
  have hdenPos : 0 < v * (1 + v) :=
    mul_pos hv.1 (by linarith [hv.1])
  have hdenLower : (3 / 4 : ℝ) ≤ v * (1 + v) := by
    have hplus : (3 / 2 : ℝ) ≤ 1 + v := by linarith
    calc
      (3 / 4 : ℝ) = (1 / 2 : ℝ) * (3 / 2 : ℝ) := by norm_num
      _ ≤ v * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hvHalf (by norm_num)
      _ ≤ v * (1 + v) := mul_le_mul_of_nonneg_left hplus hv.1.le
  have hdScaled : 1000 * d ≤ 501 * e := by nlinarith
  have hdScaled0 : 0 ≤ 1000 * d := mul_nonneg (by norm_num) hd0
  have hsquare := mul_self_le_mul_self hdScaled0 hdScaled
  have hdsq : d ^ 2 ≤ (251001 / 1000000 : ℝ) * e ^ 2 := by
    nlinarith
  have hnum : d ^ 2 ≤ e ^ 2 * (v * (1 + v)) := by
    have heSq0 : 0 ≤ e ^ 2 := sq_nonneg e
    have hdenScaled := mul_le_mul_of_nonneg_left hdenLower heSq0
    nlinarith
  unfold lrDA7ChannelKappa
  change d ^ 2 / (v * (1 + v)) ≤ e ^ 2
  rw [div_le_iff₀ hdenPos]
  simpa [mul_comm] using hnum

/-! ## A true-channel `T` envelope on the restricted band -/

lemma lrDA7_channel_deltaT_normalized_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrDA7ChannelDeltaT point / lrLowKNormalization point ≤
      4 * point.s *
        (14 / 5 + (501 / 500 : ℝ) *
          (Real.log (1 / point.s) + 7 / 5)) := by
  let s := point.s
  let e := lrCertificateE point
  let R := lrCertificateR point
  let v := lrCertificateV point
  let yR := lrCertificateB point.s (lrCertificateE point)
  let b := lrDA7ChannelB point
  let kappa := lrDA7ChannelKappa point
  let f0 := lrDA7ChannelF0 point
  let n := lrLowKNormalization point
  let L := Real.log (1 / point.s)
  let C := L + 7 / 5
  let qdiff := lrDA7LogarithmicQ yR - lrDA7LogarithmicQ s
  have hs := hinterior.1
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hs.2]
  have hyRMem : yR ∈ Ioo (0 : ℝ) 1 := by
    simpa [yR, e] using lrCertificateB_mem_Ioo hs he
  have hsyR : s < yR := by
    dsimp [s, yR]
    unfold lrCertificateB
    nlinarith [mul_pos (sub_pos.mpr hs.2) he.1]
  have hqdiff0 : 0 ≤ qdiff := by
    dsimp [qdiff]
    exact sub_nonneg.mpr
      (lrDA7_logarithmicQ_mono hs.1 hyRMem.2.le hsyR.le)
  have hqtangent := lrDA7_logarithmicQ_tangent_upper hs.1 hsyR
  have hyDiff : yR - s = R * e := by
    dsimp [yR, s, R, e]
    unfold lrCertificateB lrCertificateR
    ring
  have hlogSplit := lrLowRatio_log_four_div_split hs.1
  have hlogTwo : 2 * Real.log 2 ≤ (7 / 5 : ℝ) := by
    nlinarith [lr_log_two_millionth_bounds.2]
  have hLPos : 0 < L := by
    dsimp [L]
    have hlogTwoPos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith [lrRestrictedDeep_log_lower hinterior hdeep]
  have hC0 : 0 ≤ C := by dsimp [C]; linarith
  have hqdiffUpper : qdiff ≤ R * e / 4 * C := by
    have hscale0 : 0 ≤ R * e / 4 :=
      div_nonneg (mul_nonneg hRPos.le he.1.le) (by norm_num)
    have hscale := mul_le_mul_of_nonneg_left
      (add_le_add_left hlogTwo L) hscale0
    dsimp [qdiff, yR, s] at hqtangent
    rw [hyDiff] at hqtangent
    unfold lrDA7LogarithmicQPrime at hqtangent
    rw [hlogSplit] at hqtangent
    dsimp [R, e, C, L] at hscale ⊢
    nlinarith [hqtangent, hscale]
  have hqYUpper : lrDA7LogarithmicQ yR ≤ Real.log 2 :=
    lrDA7_logarithmicQ_le_log_two ⟨hyRMem.1, hyRMem.2.le⟩
  have hbBounds := lrDA7_channel_b_bounds_oneToFour
    hinterior hdeep hkOne hkFour
  have hb0 : 0 ≤ b := by simpa [b] using hbBounds.1
  have hbUpper : b ≤ (501 / 500 : ℝ) * e := by
    simpa [b, e] using hbBounds.2
  have hk0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hkUpper : kappa ≤ e ^ 2 := by
    simpa [kappa, e] using
      lrDA7_channel_kappa_le_e_sq_oneToFour hinterior hdeep hkOne hkFour
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (7 / 10 : ℝ) :=
    lr_log_two_millionth_bounds.2.le.trans (by norm_num)
  have hg0 : lrCertificateG0 v ≤ 0 :=
    lrCertificateG0_nonpos_Ioc ⟨hv.1, hv.2.le⟩
  have hf0Upper : f0 ≤ (7 / 10 : ℝ) * e ^ 2 := by
    have hklog := mul_le_mul hkUpper hlogUpper hlog0 (sq_nonneg e)
    dsimp [f0, v, kappa, e]
    unfold lrDA7ChannelF0
    nlinarith [hg0, hklog]
  have hkQ :
      kappa * (lrDA7LogarithmicQ yR - Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hk0 (sub_nonpos.mpr hqYUpper)
  have hqUpper0 : 0 ≤ R * e / 4 * C :=
    mul_nonneg
      (div_nonneg (mul_nonneg hRPos.le he.1.le) (by norm_num)) hC0
  have hbUpper0 : 0 ≤ (501 / 500 : ℝ) * e :=
    mul_nonneg (by norm_num) he.1.le
  have hbq := mul_le_mul hbUpper hqdiffUpper hqdiff0 hbUpper0
  have hbq' : b * qdiff ≤
      (501 / 2000 : ℝ) * e ^ 2 * R * C := by
    dsimp [b, qdiff, e, R, C] at hbq ⊢
    nlinarith [hbq]
  have hchannelDiv :
      (b * qdiff +
          kappa * (lrDA7LogarithmicQ yR - Real.log 2)) / R ≤
        (501 / 2000 : ℝ) * e ^ 2 * C := by
    rw [div_le_iff₀ hRPos]
    nlinarith [hbq', hkQ]
  have hdeltaRaw : lrDA7ChannelDeltaT point ≤
      (7 / 10 : ℝ) * e ^ 2 + (501 / 2000 : ℝ) * e ^ 2 * C := by
    unfold lrDA7ChannelDeltaT
    dsimp [f0, b, qdiff, kappa, yR, R, e, C] at hf0Upper hchannelDiv
    dsimp [f0, b, qdiff, kappa, yR, R, e, C]
    nlinarith
  have hnPos : 0 < n := by
    simpa [n] using lrLowKNormalization_pos hinterior
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg he.1.le hinterior.2.2.1.le]
  have hfactor : 0 ≤ 14 / 5 + (501 / 500 : ℝ) * C :=
    add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC0)
  have hfactor0 : 0 ≤ e * (14 / 5 + (501 / 500 : ℝ) * C) :=
    mul_nonneg he.1.le hfactor
  have hrawToN :
      (7 / 10 : ℝ) * e ^ 2 + (501 / 2000 : ℝ) * e ^ 2 * C ≤
        e * (14 / 5 + (501 / 500 : ℝ) * C) * n := by
    have hscaled := mul_le_mul_of_nonneg_left hnLower hfactor0
    calc
      (7 / 10 : ℝ) * e ^ 2 + (501 / 2000 : ℝ) * e ^ 2 * C =
          e * (14 / 5 + (501 / 500 : ℝ) * C) * (e / 4) := by ring
      _ ≤ e * (14 / 5 + (501 / 500 : ℝ) * C) * n := hscaled
  have hnormalized :
      lrDA7ChannelDeltaT point / n ≤
        e * (14 / 5 + (501 / 500 : ℝ) * C) := by
    rw [div_le_iff₀ hnPos]
    exact hdeltaRaw.trans hrawToN
  have heFour : e ≤ 4 * s := by
    simpa [e, s] using lrRestrictedDeep_e_le_four_s hinterior hkFour
  have hescaled := mul_le_mul_of_nonneg_right heFour hfactor
  simpa [n, e, s, C, L, mul_assoc] using hnormalized.trans hescaled

lemma lrDA7_channel_deltaT_upper_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrDA7ChannelDeltaT point / lrLowKNormalization point ≤ (1 / 10 : ℝ) := by
  let s0 : ℝ := 1 / 16384
  let L := Real.log (1 / point.s)
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hpoint := lrDA7_channel_deltaT_normalized_oneToFour
    hinterior hdeep hkOne hkFour
  have hs0Pos : 0 < s0 := by norm_num [s0]
  have hendpointLog : Real.log (1 / s0) = 14 * Real.log 2 := by
    dsimp [s0]
    rw [show (1 / (1 / 16384 : ℝ)) = 2 ^ 14 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (1 / s0) := by
    rw [hendpointLog]
    nlinarith [lr_log_two_millionth_bounds.1]
  have hmul := lrDA7_mul_log_inv_le_endpoint
    hs.1 hs0Pos hs.2 hendpointOne
  rw [hendpointLog] at hmul
  have hlogUpper := lr_log_two_millionth_bounds.2.le
  have hsUpper : point.s ≤ s0 := by simpa [s0] using hs.2
  calc
    lrDA7ChannelDeltaT point / lrLowKNormalization point ≤
        4 * point.s *
          (14 / 5 + (501 / 500 : ℝ) *
            (Real.log (1 / point.s) + 7 / 5)) := hpoint
    _ ≤ (1 / 10 : ℝ) := by
      dsimp [s0] at hsUpper hmul
      nlinarith

lemma lrDA7_finiteT_upper_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7FiniteT point ≤ Real.log (1 / point.s) + 7 / 5 := by
  have hAH := lrDA7FiniteAH_ge_one hinterior
  have hlogUpper := lr_log_two_millionth_bounds.2.le
  unfold lrDA7FiniteT
  nlinarith

lemma lrDA7_channelT_upper_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrDA7ChannelT point ≤ Real.log (1 / point.s) + 3 / 2 := by
  have hfinite := lrDA7_finiteT_upper_oneToFour (point := point) hinterior
  have hdelta := lrDA7_channel_deltaT_upper_oneToFour
    hinterior hdeep hkOne hkFour
  unfold lrDA7ChannelT
  linarith

/-! ## Exact entropy-coefficient endpoint -/

lemma lrDA7_channel_c0q_sub_c0_bounds_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    0 ≤ lrDA7ChannelC0Q point - lrDeterminantC0 point ∧
      lrDA7ChannelC0Q point - lrDeterminantC0 point ≤
        4 * lrLowerFaceR0Prime point.s * lrDA7ChannelC0Q point := by
  let H := lrDA7ChannelH point
  let Hd := lrDeterminantHd point
  let r := lrLowerFaceR0 point.s
  let rp := lrLowerFaceR0Prime point.s
  let cq := lrDA7ChannelC0Q point
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hLPos : 0 < Real.log (1 / point.s) := by
    have hlogTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith [lrRestrictedDeep_log_lower hinterior hdeep]
  have hHLower : Real.log (1 / point.s) ≤ H := by
    simpa [H] using lrDA7_channel_H_ge_log_scale hinterior
  have hH : 1 ≤ H := by
    have hlogTwo := lr_log_two_millionth_bounds.1.le
    have hL := lrRestrictedDeep_log_lower hinterior hdeep
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

lemma lrDA7_channel_c0q_sub_c0_pointwise_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    lrDA7ChannelC0Q point - lrDeterminantC0 point ≤
      point.s * (Real.log (1 / point.s) + 7 / 5) /
        (2 * Real.log (1 / point.s)) := by
  let L := Real.log (1 / point.s)
  let H := lrDA7ChannelH point
  let rp := lrLowerFaceR0Prime point.s
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hLPos : 0 < L := by
    dsimp [L]
    have hlogTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith [lrRestrictedDeep_log_lower hinterior hdeep]
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
  have hcoeff :=
    (lrDA7_channel_c0q_sub_c0_bounds_oneToFour hinterior hdeep).2
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
    ⟨hinterior.1.1, hs.2.trans_lt (by norm_num)⟩
  have hrpRaw := lrLowerFaceR0Prime_upper hs16
  have hlogSplit := lrLowRatio_log_four_div_split hinterior.1.1
  have hrp : rp ≤ point.s / 3 * (L + 7 / 5) := by
    have hlogTwo : 2 * Real.log 2 ≤ (7 / 5 : ℝ) := by
      nlinarith [lr_log_two_millionth_bounds.2]
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

lemma lrDA7_entropy_restricted_endpoint_numeric :
    (1 / 16384 : ℝ) * lrDA7PEnt (14 * Real.log 2) /
        (2 * (14 * Real.log 2)) ≤
      lrBoundedDeepEntropyCoefficientEndpoint := by
  let L0 := 14 * Real.log 2
  let Llo : ℝ := 14 * (693147 / 1000000 : ℝ)
  let Lhi : ℝ := 14 * (693148 / 1000000 : ℝ)
  have hlog := lr_log_two_millionth_bounds
  have hLlo : Llo ≤ L0 := by dsimp [Llo, L0]; nlinarith [hlog.1]
  have hLhi : L0 ≤ Lhi := by dsimp [Lhi, L0]; nlinarith [hlog.2]
  have hL0Pos : 0 < L0 := by
    dsimp [L0]
    positivity
  have hA0 : 0 ≤ L0 + 7 / 5 := by positivity
  have hB0 : 0 ≤ L0 / 2 + 7 / 10 + 1 / 256 := by positivity
  have hC0 : 0 ≤ L0 + 3 / 2 := by positivity
  have hAhi : 0 ≤ Lhi + 7 / 5 := by norm_num [Lhi]
  have hBhi : 0 ≤ Lhi / 2 + 7 / 10 + 1 / 256 := by norm_num [Lhi]
  have hA : L0 + 7 / 5 ≤ Lhi + 7 / 5 := by linarith
  have hB : L0 / 2 + 7 / 10 + 1 / 256 ≤
      Lhi / 2 + 7 / 10 + 1 / 256 := by linarith
  have hC : L0 + 3 / 2 ≤ Lhi + 3 / 2 := by linarith
  have hP : lrDA7PEnt L0 ≤ lrDA7PEnt Lhi := by
    unfold lrDA7PEnt
    exact mul_le_mul (mul_le_mul hA hB hB0 hAhi) hC hC0
      (mul_nonneg hAhi hBhi)
  have hscale := mul_le_mul_of_nonneg_left hP
    (show (0 : ℝ) ≤ 1 / 16384 by norm_num)
  rw [div_le_iff₀ (mul_pos (by norm_num) hL0Pos)]
  calc
    (1 / 16384 : ℝ) * lrDA7PEnt L0 ≤
        (1 / 16384 : ℝ) * lrDA7PEnt Lhi := hscale
    _ ≤ lrBoundedDeepEntropyCoefficientEndpoint * (2 * Llo) := by
      norm_num [Lhi, Llo, lrDA7PEnt,
        lrBoundedDeepEntropyCoefficientEndpoint]
    _ ≤ lrBoundedDeepEntropyCoefficientEndpoint * (2 * L0) := by
      exact mul_le_mul_of_nonneg_left (by linarith)
        (by norm_num [lrBoundedDeepEntropyCoefficientEndpoint])

theorem lrBoundedDeep_entropyCoefficient_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrDA7TrueChannelCore point -
        lrBoundedDeepActualCoefficientQCore point ≤
      lrBoundedDeepEntropyCoefficientEndpoint := by
  let L := Real.log (1 / point.s)
  let L0 := 14 * Real.log 2
  let dc := lrDA7ChannelC0Q point - lrDeterminantC0 point
  let J := lrDA7ChannelJ1 point
  let T := lrDA7ChannelT point
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hsWide : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    exact ⟨hs.1, hs.2.trans (by norm_num [lrDA7S0])⟩
  have hsEndpointWide : (1 / 16384 : ℝ) ∈ Ioc (0 : ℝ) lrDA7S0 := by
    norm_num [lrDA7S0]
  have hLPos : 0 < L := by
    dsimp [L]
    have hlogTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith [lrRestrictedDeep_log_lower hinterior hdeep]
  have hL0Pos : 0 < L0 := by dsimp [L0]; positivity
  have hLLower : L0 ≤ L := by
    simpa [L0, L] using lrRestrictedDeep_log_lower hinterior hdeep
  have hdcBounds :=
    lrDA7_channel_c0q_sub_c0_bounds_oneToFour hinterior hdeep
  have hdc0 : 0 ≤ dc := by simpa [dc] using hdcBounds.1
  have hdc : dc ≤ point.s * (L + 7 / 5) / (2 * L) := by
    simpa [dc, L] using
      lrDA7_channel_c0q_sub_c0_pointwise_oneToFour hinterior hdeep
  have hJ0 : 0 ≤ J := by
    dsimp [J, lrDA7ChannelJ1]
    exact (lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant).le
  have hJ : J ≤ L / 2 + 7 / 10 + 1 / 256 := by
    have hraw := lrDA7_channel_j1_le_log_scale_half_add_log_two hinterior
    have hlogUpper := lr_log_two_millionth_bounds.2.le
    dsimp [J, L]
    nlinarith
  have hT : T ≤ L + 3 / 2 := by
    simpa [T, L] using
      lrDA7_channelT_upper_oneToFour hinterior hdeep hkOne hkFour
  have hJMax0 : 0 ≤ L / 2 + 7 / 10 + 1 / 256 := by positivity
  have hdcMax0 : 0 ≤ point.s * (L + 7 / 5) / (2 * L) :=
    div_nonneg
      (mul_nonneg hinterior.1.1.le (add_nonneg hLPos.le (by norm_num)))
      (mul_nonneg (by norm_num) hLPos.le)
  have hmono := lrDA7PEntWeight_monotoneOn hsWide hsEndpointWide hs.2
  have hendpointLog :
      Real.log (1 / (1 / 16384 : ℝ)) = L0 := by
    dsimp [L0]
    rw [show (1 / (1 / 16384 : ℝ)) = 2 ^ 14 by norm_num,
      Real.log_pow]
    norm_num
  unfold lrDA7PEntWeight at hmono
  rw [hendpointLog] at hmono
  have hweight0 : 0 ≤ (1 / 16384 : ℝ) * lrDA7PEnt L0 := by
    unfold lrDA7PEnt
    positivity
  have hendpoint : point.s * lrDA7PEnt L / (2 * L) ≤
      (1 / 16384 : ℝ) * lrDA7PEnt L0 / (2 * L0) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hLPos)
      (mul_pos (by norm_num) hL0Pos)]
    have hcross := mul_le_mul hmono hLLower hL0Pos.le hweight0
    nlinarith [hcross]
  rw [lrBoundedDeep_trueQ_sub_actualQCoefficient]
  by_cases hT0 : 0 ≤ T
  · have hprod : dc * J * T ≤ point.s * lrDA7PEnt L / (2 * L) := by
      have h1 := mul_le_mul hdc hJ hJ0 hdcMax0
      have h2 := mul_le_mul h1 hT hT0
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
      _ ≤ (1 / 16384 : ℝ) * lrDA7PEnt L0 / (2 * L0) := hendpoint
      _ ≤ lrBoundedDeepEntropyCoefficientEndpoint :=
        lrDA7_entropy_restricted_endpoint_numeric
  · have hprodNonpos : dc * J * T ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hdc0 hJ0)
        (le_of_not_ge hT0)
    have hbudget0 : 0 ≤ lrBoundedDeepEntropyCoefficientEndpoint := by
      norm_num [lrBoundedDeepEntropyCoefficientEndpoint]
    dsimp [dc, J, T] at hprodNonpos
    exact hprodNonpos.trans hbudget0

/-! ## Direct `Q = q+r` endpoint -/

lemma lrDA7_D1_add_BFlow_upper_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrDeterminantD1 point + lrCertificateBFlow point ≤
      Real.log (1 / point.s) + 4 / 5 := by
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hk := lrRestrictedDeep_kBand hkOne hkFour
  have hD1 := lrDeterminantD1_le_D hinterior
  have hD := lrSmallSBridgeD_mem hs hk
  have hDEq := lrCertificateD_eq_smallSBridgeD
    (s := point.s) (k := point.k) (chi := point.chi) hs hk
  have hDUpper : lrCertificateD point ≤ (5 / 6 : ℝ) := by
    rw [hDEq]
    exact hD.2
  have hB := lrCertificateBFlow_le_log_scale_half_add_log_two hinterior
  have hL := lrRestrictedDeep_log_lower hinterior hdeep
  have hlogLower := lr_log_two_millionth_bounds.1.le
  have hlogUpper := lr_log_two_millionth_bounds.2.le
  nlinarith

lemma lrBoundedDeep_directOmegaCost_pointwise_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    (lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point ≤
      (16 / 3 : ℝ) * point.s ^ 3 *
        lrDA7PDir (Real.log (1 / point.s)) := by
  let e := lrCertificateE point
  let n := lrLowKNormalization point
  let A := lrDeterminantD1 point + lrCertificateBFlow point
  let kappa := lrDA7ChannelKappa point
  let rp := lrLowerFaceR0Prime point.s
  let L := Real.log (1 / point.s)
  have hs := lrRestrictedDeep_smallS hinterior hdeep
  have hs16 : point.s ∈ Ioo (0 : ℝ) (1 / 16) :=
    ⟨hinterior.1.1, hs.2.trans_lt (by norm_num)⟩
  have he := hinterior.2.1
  have heFour : e ≤ 4 * point.s := by
    simpa [e] using lrRestrictedDeep_e_le_four_s hinterior hkFour
  have hnPos : 0 < n := by
    simpa [n] using lrLowKNormalization_pos hinterior
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le hinterior.2.2.1.le]
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (lrDeterminantD1_nonnegative hinterior)
      (lrCertificateBFlow_pos hinterior).le
  have hA : A ≤ L + 4 / 5 := by
    simpa [A, L] using
      lrDA7_D1_add_BFlow_upper_oneToFour hinterior hdeep hkOne hkFour
  have hk0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hk : kappa ≤ e ^ 2 := by
    simpa [kappa, e] using
      lrDA7_channel_kappa_le_e_sq_oneToFour hinterior hdeep hkOne hkFour
  have hrp0 : 0 ≤ rp := by
    simpa [rp] using lrLowerFaceR0Prime_nonneg hinterior.1
  have hlogSplit : Real.log (4 / point.s) = L + 2 * Real.log 2 := by
    dsimp [L]
    rw [show 4 / point.s = 4 * (1 / point.s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hinterior.1.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  have hrpRaw := lrLowerFaceR0Prime_upper hs16
  have hrp : rp ≤ point.s / 3 * (L + 7 / 5) := by
    rw [hlogSplit] at hrpRaw
    have hlogTwo : 2 * Real.log 2 ≤ (7 / 5 : ℝ) := by
      nlinarith [lr_log_two_millionth_bounds.2]
    have hsThird : 0 ≤ point.s / 3 :=
      div_nonneg hinterior.1.1.le (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left
      (add_le_add_left hlogTwo L) hsThird
    have hscaled' :
        point.s / 3 * (L + 2 * Real.log 2) ≤
          point.s / 3 * (L + 7 / 5) := by
      simpa [add_comm] using hscaled
    simpa [rp] using hrpRaw.trans hscaled'
  have hL0 : 0 ≤ L := by
    have hlogTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [L]
    linarith [lrRestrictedDeep_log_lower hinterior hdeep]
  have hP0 : 0 ≤ lrDA7PDir L := by
    unfold lrDA7PDir
    positivity
  have hnumerator :
      A * kappa * point.s * rp ≤
        e ^ 2 * point.s ^ 2 / 3 * lrDA7PDir L := by
    have hAk : A * kappa ≤ (L + 4 / 5) * e ^ 2 :=
      mul_le_mul hA hk hk0 (by linarith)
    have hAks := mul_le_mul_of_nonneg_right hAk hinterior.1.1.le
    have hAks0 : 0 ≤ A * kappa * point.s :=
      mul_nonneg (mul_nonneg hA0 hk0) hinterior.1.1.le
    have hAksUpper0 : 0 ≤ (L + 4 / 5) * e ^ 2 * point.s :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg e))
        hinterior.1.1.le
    have hleft := mul_le_mul hAks hrp hrp0 hAksUpper0
    calc
      A * kappa * point.s * rp ≤
          (L + 4 / 5) * e ^ 2 * point.s *
            (point.s / 3 * (L + 7 / 5)) := hleft
      _ = e ^ 2 * point.s ^ 2 / 3 * lrDA7PDir L := by
        unfold lrDA7PDir
        ring
  have heSq : e ^ 2 ≤ 4 * e * point.s := by
    nlinarith [mul_nonneg he.1.le (sub_nonneg.mpr heFour)]
  have hfactor0 : 0 ≤ point.s ^ 2 / 3 * lrDA7PDir L := by positivity
  have heStep := mul_le_mul_of_nonneg_right heSq hfactor0
  have htarget0 :
      0 ≤ (16 / 3 : ℝ) * point.s ^ 3 * lrDA7PDir L := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hinterior.1.1.le 3)) hP0
  have hnStep := mul_le_mul_of_nonneg_left hnLower htarget0
  have hcleared :
      A * kappa * point.s * rp ≤
        ((16 / 3 : ℝ) * point.s ^ 3 * lrDA7PDir L) * n := by
    calc
      A * kappa * point.s * rp ≤
          e ^ 2 * point.s ^ 2 / 3 * lrDA7PDir L := hnumerator
      _ ≤ (4 * e * point.s) *
          (point.s ^ 2 / 3 * lrDA7PDir L) := by
        simpa [div_eq_mul_inv, mul_assoc] using heStep
      _ = ((16 / 3 : ℝ) * point.s ^ 3 * lrDA7PDir L) * (e / 4) := by ring
      _ ≤ ((16 / 3 : ℝ) * point.s ^ 3 * lrDA7PDir L) * n := hnStep
  unfold lrBoundedDeepDirectOmegaCost
  dsimp [A, kappa, rp, n, L] at hcleared ⊢
  rw [show
      (lrDeterminantD1 point + lrCertificateBFlow point) *
          (lrDA7ChannelKappa point * point.s *
            lrLowerFaceR0Prime point.s / lrLowKNormalization point) =
        ((lrDeterminantD1 point + lrCertificateBFlow point) *
          lrDA7ChannelKappa point * point.s *
            lrLowerFaceR0Prime point.s) / lrLowKNormalization point by ring]
  exact (div_le_iff₀ hnPos).2 hcleared

lemma lrDA7_direct_restricted_endpoint_numeric
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384)) :
    (16 / 3 : ℝ) * s ^ 3 * lrDA7PDir (Real.log (1 / s)) ≤
      lrBoundedDeepDirectRemainderEndpoint := by
  let s0 : ℝ := 1 / 16384
  let L0 := 14 * Real.log 2
  let Lhi : ℝ := 14 * (693148 / 1000000 : ℝ)
  have hsWide : s ∈ Ioc (0 : ℝ) lrDA7S0 :=
    ⟨hs.1, hs.2.trans (by norm_num [lrDA7S0])⟩
  have hsEndpointWide : s0 ∈ Ioc (0 : ℝ) lrDA7S0 := by
    norm_num [s0, lrDA7S0]
  have hmono := lrDA7PDirWeight_monotoneOn
    hsWide hsEndpointWide (by simpa [s0] using hs.2)
  have hendpointLog : Real.log (1 / s0) = L0 := by
    dsimp [s0, L0]
    rw [show (1 / (1 / 16384 : ℝ)) = 2 ^ 14 by norm_num,
      Real.log_pow]
    norm_num
  unfold lrDA7PDirWeight at hmono
  rw [hendpointLog] at hmono
  have hLhi : L0 ≤ Lhi := by
    dsimp [L0, Lhi]
    nlinarith [lr_log_two_millionth_bounds.2]
  have hleft0 : 0 ≤ L0 + 4 / 5 := by positivity
  have hright0 : 0 ≤ L0 + 7 / 5 := by positivity
  have hleftHi0 : 0 ≤ Lhi + 4 / 5 := by norm_num [Lhi]
  have hP : lrDA7PDir L0 ≤ lrDA7PDir Lhi := by
    have hleft : L0 + 4 / 5 ≤ Lhi + 4 / 5 :=
      by simpa [add_comm] using add_le_add_right hLhi (4 / 5)
    have hright : L0 + 7 / 5 ≤ Lhi + 7 / 5 :=
      by simpa [add_comm] using add_le_add_right hLhi (7 / 5)
    unfold lrDA7PDir
    exact mul_le_mul hleft hright hright0 hleftHi0
  have hPscaled := mul_le_mul_of_nonneg_left hP
    (pow_nonneg (show 0 ≤ s0 by norm_num [s0]) 3)
  have hweight :
      s ^ 3 * lrDA7PDir (Real.log (1 / s)) ≤
        s0 ^ 3 * lrDA7PDir Lhi := hmono.trans hPscaled
  have hscaled := mul_le_mul_of_nonneg_left hweight
    (by norm_num : (0 : ℝ) ≤ 16 / 3)
  calc
    (16 / 3 : ℝ) * s ^ 3 * lrDA7PDir (Real.log (1 / s)) ≤
        (16 / 3 : ℝ) * s0 ^ 3 * lrDA7PDir Lhi := by
      simpa [mul_assoc] using hscaled
    _ ≤ lrBoundedDeepDirectRemainderEndpoint := by
      norm_num [s0, Lhi, lrDA7PDir,
        lrBoundedDeepDirectRemainderEndpoint]

theorem lrBoundedDeep_directRemainderCost_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    (lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point ≤
      lrBoundedDeepDirectRemainderEndpoint := by
  have hpoint := lrBoundedDeep_directOmegaCost_pointwise_oneToFour
    hinterior hdeep hkOne hkFour
  have hendpoint := lrDA7_direct_restricted_endpoint_numeric
    (lrRestrictedDeep_smallS hinterior hdeep)
  exact hpoint.trans hendpoint

theorem lrBoundedDeep_directRemainder_oneToFour
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k) (hkFour : point.k ≤ 4) :
    lrBoundedDeepActualCoefficientQCore point -
        lrLowKActualNormalized point ≤
      lrBoundedDeepDirectRemainderEndpoint := by
  have hsigns := lrBoundedDeep_directRemainderSigns_lowK hinterior hrelevant
  have hraw := lrBoundedDeep_qCore_sub_actual_le_directCost
    (lrLowKNormalization_pos hinterior).ne'
    (lrBoundedDeep_qChannelIdentification hinterior) hsigns
  exact hraw.trans
    (lrBoundedDeep_directRemainderCost_oneToFour
      hinterior hdeep hkOne hkFour)

/-! ## Specialized four-stage assembly -/

/-- Only the two stages preceding the now-proved entropy and direct endpoints
remain as inputs on the restricted deep band. -/
structure LRDeterminantDeepOneToFourFirstTwoStages : Prop where
  finite : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantDeepRegion point →
    1 ≤ point.k →
    point.k ≤ 4 →
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point ≤
      lrBoundedDeepLowFiniteEndpoint
  channelPayments : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantDeepRegion point →
    1 ≤ point.k →
    point.k ≤ 4 →
    LRBoundedDeepTrueChannelPayments point
      (lrBoundedDeepLowDeltaGLoss point)
  channelEndpoint : ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRDeterminantDeepRegion point →
    1 ≤ point.k →
    point.k ≤ 4 →
    lrBoundedDeepChannelPointwiseLoss point
        (lrBoundedDeepLowDeltaGLoss point) ≤
      lrBoundedDeepLowChannelEndpoint

theorem lrDeterminantDeepOneToFourRestoration_of_firstTwoStages
    (inputs : LRDeterminantDeepOneToFourFirstTwoStages) :
    LRDeterminantDeepOneToFourRestorationTheorem := by
  intro point hinterior hrelevant hdeep hkOne hkFour
  have hfinite := inputs.finite point hinterior hrelevant hdeep hkOne hkFour
  have hpayments := inputs.channelPayments point hinterior hrelevant
    hdeep hkOne hkFour
  have hchannelRaw := lrBoundedDeep_trueChannel_loss hpayments
  have hchannelEndpoint := inputs.channelEndpoint point hinterior
    hdeep hkOne hkFour
  have hchannel :
      lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point ≤
        lrBoundedDeepLowChannelEndpoint :=
    hchannelRaw.trans hchannelEndpoint
  have hcoefficient := lrBoundedDeep_entropyCoefficient_oneToFour
    hinterior hrelevant hdeep hkOne hkFour
  have hdirect := lrBoundedDeep_directRemainder_oneToFour
    hinterior hrelevant hdeep hkOne hkFour
  have hsum := lrBoundedDeep_loss_of_four_stages
    hfinite hchannel hcoefficient hdirect
  calc
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrLowKActualNormalized point ≤
        lrBoundedDeepLowFiniteEndpoint +
          lrBoundedDeepLowChannelEndpoint +
          lrBoundedDeepEntropyCoefficientEndpoint +
          lrBoundedDeepDirectRemainderEndpoint := hsum
    _ = (lrDeterminantLowBandRestorationBudget : ℝ) :=
      lrBoundedDeep_low_budget_sum

end CourtadeKumar
