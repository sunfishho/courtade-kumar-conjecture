import InformationTheory.CourtadeKumar.LRDeterminantBoundedDeepRestoration

/-!
# Positive-side normalized `Delta T` envelope on the low-`k` row

This module proves the analytic upper bound on the true-channel increase in
the normalized radial factor.  The pointwise estimate is paid by the audited
small-`s` endpoint inequality, yielding `Delta T / n <= 1/10` and hence the
channel bound `T <= log (1/s) + 3/2`.
-/

open Set

namespace CourtadeKumar

lemma lrCertificateG0_monotoneOn_Ioc :
    MonotoneOn lrCertificateG0 (Ioc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) 1)
  · intro v hv
    exact (hasDerivAt_lrCertificateG0 hv.1).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioc] at hv
    exact (hasDerivAt_lrCertificateG0 hv.1).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Ioc] at hv
    rw [(hasDerivAt_lrCertificateG0 hv.1).deriv]
    unfold lrCertificateG0Prime
    exact div_nonneg
      (sub_nonneg.mpr
        (Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])))
      (sq_nonneg v)

lemma lrCertificateG0_nonpos_Ioc
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrCertificateG0 v ≤ 0 := by
  have h := lrCertificateG0_monotoneOn_Ioc hv
    (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num) hv.2
  have hone : lrCertificateG0 (1 : ℝ) = 0 := by
    norm_num [lrCertificateG0]
  rw [hone] at h
  exact h

lemma lrDA7_logarithmicQ_le_log_two
    {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    lrDA7LogarithmicQ y ≤ Real.log 2 := by
  have hmono := lrDA7_logarithmicQ_mono hy.1 (by norm_num) hy.2
  have hone : lrDA7LogarithmicQ (1 : ℝ) ≤ Real.log 2 := by
    unfold lrDA7LogarithmicQ
    have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [show (4 : ℝ) / 1 = 4 by norm_num]
    rw [hlogFour]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  exact hmono.trans hone

lemma lrDA7_logarithmicQ_tangent_upper
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    lrDA7LogarithmicQ b - lrDA7LogarithmicQ a ≤
      (b - a) * lrDA7LogarithmicQPrime a := by
  have hmem : ∀ y ∈ Icc a b, 0 < y := by
    intro y hy
    exact ha.trans_le hy.1
  have hq : ∀ y ∈ Icc a b,
      HasDerivAt lrLowerFaceQ0 (lrLowerFaceQ0Prime y) y :=
    fun y hy ↦ hasDerivAt_lrLowerFaceQ0 (hmem y hy)
  have hqp : ∀ y ∈ Icc a b,
      HasDerivAt lrLowerFaceQ0Prime (lrLowerFaceQ0Second y) y :=
    fun y hy ↦ hasDerivAt_lrLowerFaceQ0Prime (hmem y hy)
  have hconcave : ConcaveOn ℝ (Icc a b) lrLowerFaceQ0 := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
    · exact continuousOn_of_forall_continuousAt fun y hy ↦ (hq y hy).continuousAt
    · intro y hy
      exact (hq y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      exact (hqp y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      unfold lrLowerFaceQ0Second
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (hmem y (interior_subset hy)).le)
  have hslope := hconcave.slope_le_of_hasDerivAt
    (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) hab
    (hasDerivAt_lrLowerFaceQ0 ha)
  rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hab)] at hslope
  simpa [lrDA7LogarithmicQ, lrDA7LogarithmicQPrime,
    lrLowerFaceQ0, lrLowerFaceQ0Prime, mul_comm] using hslope

lemma lrDA7_channel_deltaT_normalized_pointwise
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelDeltaT point / lrLowKNormalization point ≤
      point.s *
        (2 / 5 + 51 / 100 *
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
    nlinarith [Real.log_two_lt_d9]
  have hC0 : 0 ≤ C := by
    dsimp [C, L]
    have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
      simpa [lrDA7S0] using And.intro hs.1 hregion.1
    linarith [lrDA7_log_scale_pos hsIoc]
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
  have hbBounds := lrDA7_channel_b_bounds hinterior hregion
  have hb0 : 0 ≤ b := by simpa [b] using hbBounds.1
  have hbUpper : b ≤ (51 / 100 : ℝ) * e := by
    simpa [b, e] using hbBounds.2
  have hk0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hkUpper : kappa ≤ e ^ 2 / 7 := by
    simpa [kappa, e] using lrDA7_channel_kappa_le_seventh hinterior hregion
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (7 / 10 : ℝ) :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hg0 : lrCertificateG0 v ≤ 0 :=
    lrCertificateG0_nonpos_Ioc ⟨hv.1, hv.2.le⟩
  have hf0Upper : f0 ≤ e ^ 2 / 10 := by
    have hklog := mul_le_mul hkUpper hlogUpper hlog0
      (div_nonneg (sq_nonneg e) (by norm_num))
    dsimp [f0, v, kappa, e]
    unfold lrDA7ChannelF0
    nlinarith [hg0, hklog]
  have hkQ :
      kappa * (lrDA7LogarithmicQ yR - Real.log 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hk0 (sub_nonpos.mpr hqYUpper)
  have hqUpper0 : 0 ≤ R * e / 4 * C :=
    mul_nonneg
      (div_nonneg (mul_nonneg hRPos.le he.1.le) (by norm_num)) hC0
  have hbUpper0 : 0 ≤ (51 / 100 : ℝ) * e :=
    mul_nonneg (by norm_num) he.1.le
  have hbq := mul_le_mul hbUpper hqdiffUpper hqdiff0 hbUpper0
  have hbq' : b * qdiff ≤
      (51 / 400 : ℝ) * e ^ 2 * R * C := by
    dsimp [b, qdiff, e, R, C] at hbq ⊢
    nlinarith [hbq]
  have hchannelDiv :
      (b * qdiff +
          kappa * (lrDA7LogarithmicQ yR - Real.log 2)) / R ≤
        (51 / 400 : ℝ) * e ^ 2 * C := by
    rw [div_le_iff₀ hRPos]
    nlinarith [hbq', hkQ]
  have hdeltaRaw : lrDA7ChannelDeltaT point ≤
      e ^ 2 / 10 + (51 / 400 : ℝ) * e ^ 2 * C := by
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
  have hfactor : 0 ≤ 2 / 5 + 51 / 100 * C :=
    add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC0)
  have hfactor0 :
      0 ≤ e * (2 / 5 + 51 / 100 * C) :=
    mul_nonneg he.1.le hfactor
  have hrawToN :
      e ^ 2 / 10 + (51 / 400 : ℝ) * e ^ 2 * C ≤
        e * (2 / 5 + 51 / 100 * C) * n := by
    have hscaled := mul_le_mul_of_nonneg_left hnLower hfactor0
    calc
      e ^ 2 / 10 + (51 / 400 : ℝ) * e ^ 2 * C =
          e * (2 / 5 + 51 / 100 * C) * (e / 4) := by ring
      _ ≤ e * (2 / 5 + 51 / 100 * C) * n := hscaled
  have hnormalized :
      lrDA7ChannelDeltaT point / n ≤
        e * (2 / 5 + 51 / 100 * C) := by
    rw [div_le_iff₀ hnPos]
    exact hdeltaRaw.trans hrawToN
  have heS : e ≤ s := by
    simpa [e, s] using lrDA7_channel_e_le_s hinterior hregion
  have hescaled := mul_le_mul_of_nonneg_right heS hfactor
  simpa [n, e, s, C, L] using hnormalized.trans hescaled

theorem lrDA7_channel_deltaT_normalized_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelDeltaT point / lrLowKNormalization point ≤
      (1 / 10 : ℝ) := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hpoint := lrDA7_channel_deltaT_normalized_pointwise hinterior hregion
  have hlog := lrDA7_s_mul_log_upper hsIoc
  have hs := hsIoc.2
  have hendpoint := lrDA7_delta_t_positive_endpoint
  have hbound :
      point.s *
          (2 / 5 + 51 / 100 *
            (Real.log (1 / point.s) + 7 / 5)) ≤
        lrDA7S0 *
          (2 / 5 + 51 / 100 * (lrDA7LPlus + 7 / 5)) := by
    nlinarith [mul_le_mul_of_nonneg_left hs
      (by norm_num : (0 : ℝ) ≤ 2 / 5 + 51 / 100 * (7 / 5))]
  calc
    lrDA7ChannelDeltaT point / lrLowKNormalization point ≤
        point.s *
          (2 / 5 + 51 / 100 *
            (Real.log (1 / point.s) + 7 / 5)) := hpoint
    _ ≤ lrDA7S0 *
          (2 / 5 + 51 / 100 * (lrDA7LPlus + 7 / 5)) := hbound
    _ = (3613 / 128000 : ℝ) := hendpoint.1
    _ ≤ 1 / 10 := hendpoint.2.le

lemma lrDA7_channelT_upper_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDA7ChannelT point ≤ Real.log (1 / point.s) + 3 / 2 := by
  have hfinite := (lrDA7FiniteT_bounds_lowK hinterior hregion).2
  have hdelta := lrDA7_channel_deltaT_normalized_upper hinterior hregion
  unfold lrDA7ChannelT
  linarith

end CourtadeKumar
