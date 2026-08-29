import InformationTheory.CourtadeKumar.LRDeterminantRestrictedOneToFourChannelCore

/-!
# True-channel restoration on the restricted deep band

This module proves the true-channel part of the bounded-deep
restoration on `s ≤ 2^-14` and `k ≤ 4`.  The proof retains the exact
compensation cancellation from the low-`k` argument.  The only geometric
change is that `e = s*k` is bounded by `4*s`, rather than by `s`.
-/

open Set

namespace CourtadeKumar

/-! ## Frozen-coordinate envelopes -/

lemma lrOneToFour_D1_finite_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrLowKIdealD point.k - point.s / 2 ≤ lrDeterminantD1 point ∧
      lrDeterminantD1 point ≤ lrLowKIdealD point.k := by
  have hs := hinterior.1.1
  have hk : 0 < point.k := hs.trans_le hdeep.2
  have heLt := lrOneToFour_channel_e_lt_one hinterior hdeep hkFour
  have hY : 1 ≤ 1 + 1 / point.k - point.s := by
    have hinv : point.s ≤ 1 / point.k := by
      rw [le_div_iff₀ hk]
      simpa [lrCertificateE] using heLt.le
    linarith
  have hmodel := lrDA7DModel_finite_loss hY hs.le
  have hshift :
      1 + 1 / point.k - point.s + point.s = 1 + 1 / point.k := by ring
  rw [hshift] at hmodel
  rw [lrLowKIdealD_eq_DModel hk,
    lrDeterminantD1_eq_DModel hs hk]
  exact ⟨hmodel.2, hmodel.1⟩

lemma lrOneToFour_idealB_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    lrDA7IdealB point ≤
      Real.log (1 / point.s) / 2 + 7 / 10 := by
  have hk : 0 < point.k := hinterior.1.1.trans_le hdeep.2
  have hlogK : 0 ≤ Real.log (1 + point.k) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealB lrLowKIdealBOffset
  linarith

/-! ## `Delta G` and `Delta Omega` -/

theorem lrOneToFour_channel_deltaG_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    -(51 / 100 : ℝ) * lrCertificateE point ^ 2 ≤
      lrDA7ChannelDeltaG point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  let d := 1 - v
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using
      lrOneToFour_channel_v_lower hinterior hdeep hkFour
  have hvHalf : v ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨by linarith, hv.2.le⟩
  have hg0 : -2 * d ^ 2 ≤ lrCertificateG0 v := by
    simpa [d] using lrCertificateG0_lower_quadratic hvHalf
  have hq : 0 ≤ lrDA7LogarithmicQ e := by
    simpa [lrDA7LogarithmicQ, lrLowerFaceQ0] using
      lrLowerFaceQ0_nonneg_of_mem
        (show e ∈ Ioc (0 : ℝ) 1 from ⟨he.1, he.2.le⟩)
  have hinv : 0 ≤ 1 / v - 1 := by
    rw [sub_nonneg, one_le_div₀ hv.1]
    exact hv.2.le
  have hqTerm : 0 ≤ (1 / v - 1) * lrDA7LogarithmicQ e :=
    mul_nonneg hinv hq
  have hd : 0 ≤ d := by dsimp [d]; linarith [hv.2]
  have hdUpper : d ≤ (128 / 255 : ℝ) * e := by
    simpa [d, e, v, lrDA7ChannelD] using
      lrOneToFour_channel_d_le hinterior hdeep hkFour
  have hleftNonneg : 0 ≤ 255 * d := mul_nonneg (by norm_num) hd
  have hscaled : 255 * d ≤ 128 * e := by nlinarith
  have hsquare := mul_self_le_mul_self hleftNonneg hscaled
  have hloss : 2 * d ^ 2 ≤ (51 / 100 : ℝ) * e ^ 2 := by
    nlinarith
  unfold lrDA7ChannelDeltaG
  dsimp [e, v, d] at hg0 hqTerm hloss ⊢
  nlinarith

theorem lrOneToFour_channel_deltaOmega_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    -(51 / 400 : ℝ) * lrCertificateE point * point.s ≤
      lrDA7ChannelDeltaOmega point := by
  let e := lrCertificateE point
  let omegaE := lrDA7LogarithmicOmega point.s e
  let omegaZero := lrDA7LogarithmicOmega point.s 0
  let b := lrDA7ChannelB point
  let kappa := lrDA7ChannelKappa point
  have hs := hinterior.1
  have he := hinterior.2.1
  have homegaE : 0 ≤ omegaE := by
    dsimp [omegaE, e]
    simpa [lrDA7LogarithmicOmega, lrDA7LogarithmicQ,
      lrDA7LogarithmicQPrime, lrLowerFaceOmegaQ0,
      lrLowerFaceQ0, lrLowerFaceQ0Prime] using
      lrLowerFaceOmegaQ0_nonneg hs he
  have homegaZero : omegaZero = point.s / 4 := by
    dsimp [omegaZero]
    simpa [lrDA7LogarithmicOmega, lrDA7LogarithmicQ,
      lrDA7LogarithmicQPrime, lrLowerFaceOmegaQ0,
      lrLowerFaceQ0, lrLowerFaceQ0Prime] using
      lrLowerFaceOmegaQ0_zero hs.1
  have hdiff : -point.s / 4 ≤ omegaE - omegaZero := by
    rw [homegaZero]
    linarith
  have hb := lrOneToFour_channel_b_bounds hinterior hdeep hkFour
  have hb0 : 0 ≤ b := by simpa [b] using hb.1
  have hbUpper : b ≤ (51 / 100 : ℝ) * e := by
    simpa [b, e] using hb.2
  have hfirst := mul_le_mul_of_nonneg_left hdiff hb0
  have hsQuarter : 0 ≤ point.s / 4 :=
    div_nonneg hinterior.1.1.le (by norm_num)
  have hweight := mul_le_mul_of_nonneg_right hbUpper hsQuarter
  have hnegative :
      -(51 / 400 : ℝ) * e * point.s ≤ b * (-point.s / 4) := by
    nlinarith
  have hkappa : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hkappaTerm : 0 ≤ kappa * omegaE :=
    mul_nonneg hkappa homegaE
  unfold lrDA7ChannelDeltaOmega
  dsimp [e, omegaE, omegaZero, b, kappa] at hfirst hnegative hkappaTerm ⊢
  nlinarith

theorem lrOneToFour_channel_deltaG_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    -(lrDeterminantD1 point * lrDA7ChannelDeltaG point /
        lrLowKNormalization point) ≤
      lrBoundedDeepLowDeltaGLoss point := by
  let e := lrCertificateE point
  let D := lrDeterminantD1 point
  let L := Real.log (1 / point.s)
  let n := lrLowKNormalization point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hL : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact lrDeterminantD1_nonnegative hinterior
  have hDleIdeal :=
    (lrOneToFour_D1_finite_bounds hinterior hdeep hkFour).2
  have hIdealUpper :=
    lrDA7IdealD_upper hinterior.1.1 hsIoc.2 hdeep.2
  have hDUpper : D ≤ (L + point.s) / 2 := by
    dsimp [D, L]
    exact hDleIdeal.trans hIdealUpper
  have hnPos : 0 < n := by
    dsimp [n]
    exact lrLowKNormalization_pos hinterior
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le
      hinterior.2.2.1.le]
  have hraw := lrOneToFour_channel_deltaG_lower
    hinterior hdeep hkFour
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hD0
  have hleft :
      -(D * lrDA7ChannelDeltaG point) ≤
        (51 / 100 : ℝ) * D * e ^ 2 := by
    dsimp [D, e] at hrawScaled ⊢
    nlinarith
  have hterm :
      (51 / 100 : ℝ) * D * e ^ 2 ≤
        (51 / 200 : ℝ) * e ^ 2 * (L + point.s) := by
    have hDe := mul_le_mul_of_nonneg_right hDUpper (sq_nonneg e)
    nlinarith
  let budget := (51 / 50 : ℝ) * e * (L + point.s)
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hinterior.2.1.1.le)
      (by linarith : 0 ≤ L + point.s)
  have hnScaled := mul_le_mul_of_nonneg_left hnLower hbudget
  have hbudgetEq :
      budget * (e / 4) =
        (51 / 200 : ℝ) * e ^ 2 * (L + point.s) := by
    dsimp [budget]
    ring
  rw [hbudgetEq] at hnScaled
  change -(D * lrDA7ChannelDeltaG point / n) ≤ budget
  rw [show -(D * lrDA7ChannelDeltaG point / n) =
      (-(D * lrDA7ChannelDeltaG point)) / n by ring]
  apply (div_le_iff₀ hnPos).2
  exact hleft.trans (hterm.trans hnScaled)

theorem lrOneToFour_channel_deltaOmega_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    -((lrDeterminantD1 point + lrCertificateBFlow point) *
        lrDA7ChannelDeltaOmega point / lrLowKNormalization point) ≤
      lrBoundedDeepDeltaOmegaLoss point := by
  let e := lrCertificateE point
  let A := lrDeterminantD1 point + lrCertificateBFlow point
  let L := Real.log (1 / point.s)
  let n := lrLowKNormalization point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hL : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have he := hinterior.2.1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (lrDeterminantD1_nonnegative hinterior)
      (lrCertificateBFlow_pos hinterior).le
  have hDleIdeal :=
    (lrOneToFour_D1_finite_bounds hinterior hdeep hkFour).2
  have hIdealDUpper :=
    lrDA7IdealD_upper hinterior.1.1 hsIoc.2 hdeep.2
  have hBTrue := lrCertificateBFlow_le_lrDA7FiniteB hinterior
  have hBFinite := (lrDA7FiniteB_ideal_interval hinterior).2
  have hBIdeal := lrOneToFour_idealB_upper hinterior hdeep
  have heUpper := lrOneToFour_channel_e_le_inv4096
    hinterior hdeep hkFour
  have hDUpper : lrDeterminantD1 point ≤ (L + point.s) / 2 := by
    exact hDleIdeal.trans (by simpa [L] using hIdealDUpper)
  have hBUpper : lrCertificateBFlow point ≤
      L / 2 + 7 / 10 + e / 2 := by
    calc
      lrCertificateBFlow point ≤ lrDA7FiniteB point := hBTrue
      _ ≤ lrDA7IdealB point + lrCertificateE point / 2 := hBFinite
      _ ≤ L / 2 + 7 / 10 + e / 2 := by
        simpa [L, e] using add_le_add_right hBIdeal
          (lrCertificateE point / 2)
  have hAUpper : A ≤ L + 4 / 5 := by
    dsimp [A]
    calc
      lrDeterminantD1 point + lrCertificateBFlow point ≤
          (L + point.s) / 2 + (L / 2 + 7 / 10 + e / 2) :=
        add_le_add hDUpper hBUpper
      _ ≤ L + 4 / 5 := by
        dsimp [e] at heUpper ⊢
        nlinarith [hdeep.1]
  have hnPos : 0 < n := by
    dsimp [n]
    exact lrLowKNormalization_pos hinterior
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le
      hinterior.2.2.1.le]
  have hraw := lrOneToFour_channel_deltaOmega_lower
    hinterior hdeep hkFour
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hA0
  have hleft :
      -(A * lrDA7ChannelDeltaOmega point) ≤
        (51 / 400 : ℝ) * A * e * point.s := by
    dsimp [A, e] at hrawScaled ⊢
    nlinarith
  have hterm :
      (51 / 400 : ℝ) * A * e * point.s ≤
        (51 / 400 : ℝ) * point.s * e * (L + 4 / 5) := by
    have hfactor : 0 ≤ (51 / 400 : ℝ) * e * point.s :=
      mul_nonneg (mul_nonneg (by norm_num) he.1.le)
        hinterior.1.1.le
    nlinarith [mul_le_mul_of_nonneg_left hAUpper hfactor]
  let budget := (51 / 100 : ℝ) * point.s * (L + 4 / 5)
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hinterior.1.1.le)
      (by linarith : 0 ≤ L + 4 / 5)
  have hnScaled := mul_le_mul_of_nonneg_left hnLower hbudget
  have hbudgetEq :
      budget * (e / 4) =
        (51 / 400 : ℝ) * point.s * e * (L + 4 / 5) := by
    dsimp [budget]
    ring
  rw [hbudgetEq] at hnScaled
  change -(A * lrDA7ChannelDeltaOmega point / n) ≤ budget
  rw [show -(A * lrDA7ChannelDeltaOmega point / n) =
      (-(A * lrDA7ChannelDeltaOmega point)) / n by ring]
  apply (div_le_iff₀ hnPos).2
  exact hleft.trans (hterm.trans hnScaled)

/-! ## The radial `Delta T` payment -/

theorem lrOneToFour_channel_deltaT_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    -(lrDA7ChannelKappa point * Real.log 2) /
        lrCertificateR point ≤
      lrDA7ChannelDeltaT point := by
  let e := lrCertificateE point
  let R := lrCertificateR point
  let yR := lrCertificateB point.s e
  let b := lrDA7ChannelB point
  let kappa := lrDA7ChannelKappa point
  let f0 := lrDA7ChannelF0 point
  have hs := hinterior.1
  have he := hinterior.2.1
  have hyRMem : yR ∈ Ioo (0 : ℝ) 1 := by
    simpa [yR, e] using lrCertificateB_mem_Ioo hs he
  have hyROrder : point.s ≤ yR := by
    dsimp [yR, e]
    unfold lrCertificateB
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) he.1.le]
  have hqOrder :
      lrDA7LogarithmicQ point.s ≤ lrDA7LogarithmicQ yR :=
    lrDA7_logarithmicQ_mono hs.1 hyRMem.2.le hyROrder
  have hqYR : 0 ≤ lrDA7LogarithmicQ yR := by
    simpa [lrDA7LogarithmicQ, lrLowerFaceQ0] using
      lrLowerFaceQ0_nonneg_of_mem
        (show yR ∈ Ioc (0 : ℝ) 1 from ⟨hyRMem.1, hyRMem.2.le⟩)
  have hb0 : 0 ≤ b := by
    simpa [b] using
      (lrOneToFour_channel_b_bounds hinterior hdeep hkFour).1
  have hkappa0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hf0 : 0 ≤ f0 := by
    simpa [f0] using lrDA7_channel_f0_nonnegative hinterior
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hs.2]
  have hbTerm :
      0 ≤ b *
        (lrDA7LogarithmicQ yR - lrDA7LogarithmicQ point.s) :=
    mul_nonneg hb0 (sub_nonneg.mpr hqOrder)
  have hkappaQTerm :
      0 ≤ kappa * lrDA7LogarithmicQ yR :=
    mul_nonneg hkappa0 hqYR
  have hnumLower :
      -(kappa * Real.log 2) ≤
        b * (lrDA7LogarithmicQ yR - lrDA7LogarithmicQ point.s) +
          kappa * (lrDA7LogarithmicQ yR - Real.log 2) := by
    nlinarith
  have hdivLower :=
    (div_le_div_iff_of_pos_right hRPos).2 hnumLower
  change -(kappa * Real.log 2) / R ≤
    f0 +
      (b * (lrDA7LogarithmicQ yR - lrDA7LogarithmicQ point.s) +
        kappa * (lrDA7LogarithmicQ yR - Real.log 2)) / R
  nlinarith

lemma lrOneToFour_channel_c0q_mul_j1_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point) :
    0 ≤ lrDA7ChannelC0Q point * lrDA7ChannelJ1 point ∧
      lrDA7ChannelC0Q point * lrDA7ChannelJ1 point ≤ 3 / 14 := by
  let L := Real.log (1 / point.s)
  let H := lrDA7ChannelH point
  let R := lrCertificateR point
  let J := lrDA7ChannelJ1 point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hHLower : L ≤ H := by
    simpa [L, H] using lrDA7_channel_H_ge_log_scale hinterior
  have hHPos : 0 < H := hLPos.trans_le hHLower
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hRLe : R ≤ 1 := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.1]
  have hJPos : 0 < J := by
    simpa [J, lrDA7ChannelJ1] using
      lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant
  have hJUpper : J ≤ L / 2 + Real.log 2 := by
    simpa [J, L] using
      lrDA7_channel_j1_le_log_scale_half_add_log_two hinterior
  have hLBase := lrLowK_log_scale_ge_L0 hinterior
    (hdeep.1.trans (by norm_num))
  have hSevenLog : 7 * Real.log 2 ≤ L := by
    simpa [L, lrLowKIdealL0] using hLBase
  have hc0Pos : 0 < lrDA7ChannelC0Q point := by
    unfold lrDA7ChannelC0Q
    exact div_pos hRPos (mul_pos (by norm_num) hHPos)
  constructor
  · exact mul_nonneg hc0Pos.le hJPos.le
  · have hRJ : R * J ≤ J := by
      have hscaled := mul_le_mul_of_nonneg_right hRLe hJPos.le
      simpa using hscaled
    unfold lrDA7ChannelC0Q
    rw [div_mul_eq_mul_div,
      div_le_iff₀ (mul_pos (by norm_num) hHPos)]
    calc
      R * J ≤ J := hRJ
      _ ≤ L / 2 + Real.log 2 := hJUpper
      _ ≤ (9 / 14 : ℝ) * L := by nlinarith
      _ ≤ (9 / 14 : ℝ) * H :=
        mul_le_mul_of_nonneg_left hHLower (by norm_num)
      _ = (3 / 14 : ℝ) * (3 * H) := by ring

lemma lrOneToFour_scaled_deltaT_payment_algebra
    {e R n kappa logTwo cJ deltaT : ℝ}
    (he : 0 < e)
    (hR : (127 / 128 : ℝ) ≤ R) (hn : e / 4 ≤ n)
    (hkappa0 : 0 ≤ kappa) (hkappa : kappa ≤ e ^ 2 / 7)
    (hlog0 : 0 ≤ logTwo) (hlog : logTwo ≤ 7 / 10)
    (hcJ0 : 0 ≤ cJ) (hcJ : cJ ≤ 3 / 14)
    (hdelta : -(kappa * logTwo) / R ≤ deltaT) :
    -(cJ * deltaT / n) ≤ e / 10 := by
  let A : ℝ := (3 / 14) * (1 / 7) * (7 / 10)
  let C : ℝ := A * (128 / 127)
  have hRPos : 0 < R :=
    (by norm_num : (0 : ℝ) < 127 / 128).trans_le hR
  have hnPos : 0 < n := (div_pos he (by norm_num)).trans_le hn
  have hcKappa :
      cJ * kappa ≤ (3 / 14 : ℝ) * (e ^ 2 / 7) :=
    mul_le_mul hcJ hkappa hkappa0 (by norm_num)
  have hright0 : 0 ≤ (3 / 14 : ℝ) * (e ^ 2 / 7) := by
    positivity
  have hnumRaw :
      cJ * kappa * logTwo ≤
        (3 / 14 : ℝ) * (e ^ 2 / 7) * (7 / 10) :=
    mul_le_mul hcKappa hlog hlog0 hright0
  have hnum : cJ * kappa * logTwo ≤ A * e ^ 2 := by
    dsimp [A]
    nlinarith [hnumRaw]
  have hC0 : 0 ≤ C := by dsimp [C, A]; norm_num
  have hCsmall : C < 1 / 40 := by
    dsimp [C, A]
    nlinarith [lrDA7_radial_t_factor_lt_one_tenth]
  have hRscaled :=
    mul_le_mul_of_nonneg_left hR (mul_nonneg hC0 (sq_nonneg e))
  have hAR : A * e ^ 2 ≤ C * e ^ 2 * R := by
    calc
      A * e ^ 2 = C * e ^ 2 * (127 / 128) := by
        dsimp [C]
        ring
      _ ≤ C * e ^ 2 * R := hRscaled
  have hdiv : cJ * kappa * logTwo / R ≤ C * e ^ 2 := by
    rw [div_le_iff₀ hRPos]
    exact hnum.trans hAR
  have hCpayment : C * e ^ 2 ≤ e ^ 2 / 40 := by
    have h := mul_le_mul_of_nonneg_right hCsmall.le (sq_nonneg e)
    nlinarith
  have hnPayment : e ^ 2 / 40 ≤ e / 10 * n := by
    have heTen : 0 ≤ e / 10 := div_nonneg he.le (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left hn heTen
    nlinarith
  have hpositivePayment :
      cJ * kappa * logTwo / R ≤ e / 10 * n :=
    hdiv.trans (hCpayment.trans hnPayment)
  have hscaledDelta := mul_le_mul_of_nonneg_left hdelta hcJ0
  have hnegativePayment :
      -(cJ * deltaT) ≤ cJ * kappa * logTwo / R := by
    calc
      -(cJ * deltaT) ≤ -(cJ * (-(kappa * logTwo) / R)) :=
        neg_le_neg hscaledDelta
      _ = cJ * kappa * logTwo / R := by ring
  have hcleared : -(cJ * deltaT) ≤ e / 10 * n :=
    hnegativePayment.trans hpositivePayment
  rw [show -(cJ * deltaT / n) = (-(cJ * deltaT)) / n by ring]
  exact (div_le_iff₀ hnPos).2 hcleared

theorem lrOneToFour_channel_deltaT_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    -(lrDA7ChannelC0Q point * lrDA7ChannelJ1 point *
        lrDA7ChannelDeltaT point / lrLowKNormalization point) ≤
      lrBoundedDeepDeltaTLoss point := by
  let e := lrCertificateE point
  let R := lrCertificateR point
  let n := lrLowKNormalization point
  let kappa := lrDA7ChannelKappa point
  let cJ := lrDA7ChannelC0Q point * lrDA7ChannelJ1 point
  have he := hinterior.2.1
  have hRLower : (127 / 128 : ℝ) ≤ R := by
    dsimp [R]
    unfold lrCertificateR
    nlinarith [hdeep.1]
  have hnLower : e / 4 ≤ n := by
    dsimp [e, n]
    unfold lrLowKNormalization
    nlinarith [mul_nonneg hinterior.2.1.1.le
      hinterior.2.2.1.le]
  have hkappa0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hkappaUpper : kappa ≤ e ^ 2 / 7 := by
    simpa [kappa, e] using
      lrOneToFour_channel_kappa_le_seventh hinterior hdeep hkFour
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (7 / 10 : ℝ) :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hcJBounds : 0 ≤ cJ ∧ cJ ≤ 3 / 14 := by
    simpa [cJ] using
      lrOneToFour_channel_c0q_mul_j1_bounds hinterior hrelevant hdeep
  have hdelta :
      -(kappa * Real.log 2) / R ≤ lrDA7ChannelDeltaT point := by
    simpa [kappa, R] using
      lrOneToFour_channel_deltaT_lower hinterior hdeep hkFour
  simpa [lrBoundedDeepDeltaTLoss, cJ, e, R, n, kappa] using
    lrOneToFour_scaled_deltaT_payment_algebra
      he.1 hRLower hnLower hkappa0 hkappaUpper hlog0 hlogUpper
      hcJBounds.1 hcJBounds.2 hdelta

/-! ## Compensation: the exact cancellation, with `e ≤ 4s` only at the
endpoint -/

lemma lrOneToFour_channel_halfP_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    (127 / 510 : ℝ) ≤
        lrDA7ChannelHalfP (lrCertificateV point) ∧
      lrDA7ChannelHalfP (lrCertificateV point) ≤ 1 / 4 := by
  let v := lrCertificateV point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using
      lrOneToFour_channel_v_lower hinterior hdeep hkFour
  have hden : 0 < 2 * (1 + v) := by positivity
  unfold lrDA7ChannelHalfP
  dsimp [v] at hv hvLower hden ⊢
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith [hv.2]

theorem lrOneToFour_channel_AH_gap_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7ChannelAHGap point ∧
      lrDA7ChannelAHGap point ≤
        (7168 / 7225 : ℝ) * lrCertificateE point := by
  let v := lrCertificateV point
  let p := lrDA7ChannelHalfP v
  let e := lrCertificateE point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using
      lrOneToFour_channel_v_lower hinterior hdeep hkFour
  have hp : p ∈ Icc (127 / 510 : ℝ) (1 / 4) := by
    simpa [p, v] using
      lrOneToFour_channel_halfP_bounds hinterior hdeep hkFour
  have hquarterMem : (1 / 4 : ℝ) ∈
      Icc (127 / 510 : ℝ) (1 / 4) := by norm_num
  have hanti := lrDA7ChannelAHBase_antitoneOn hp hquarterMem hp.2
  have hmono := lrDA7ChannelAHShifted_monotoneOn hp hquarterMem hp.2
  have hbaseQuarter := lrDA7ChannelAHBase_quarter
  have hgapNonnegative : 0 ≤
      lrDA7ChannelAHBase p - 16 * Real.log (4 / 3) := by
    rw [← hbaseQuarter]
    linarith
  have hgapSlope :
      lrDA7ChannelAHBase p - 16 * Real.log (4 / 3) ≤
        (63 / 4 : ℝ) * (1 / 4 - p) := by
    unfold lrDA7ChannelAHShifted at hmono
    rw [hbaseQuarter] at hmono
    linarith
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hpFormula : 1 / 4 - p = (1 - v) / (4 * (1 + v)) := by
    dsimp [p]
    unfold lrDA7ChannelHalfP
    field_simp [hplus.ne']
    ring
  have hd0 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have hdUpper : 1 - v ≤ (128 / 255 : ℝ) * e := by
    simpa [v, e, lrDA7ChannelD] using
      lrOneToFour_channel_d_le hinterior hdeep hkFour
  have hinvUpper : 1 / (1 + v) ≤ (128 / 255 : ℝ) := by
    have hdenLower : (255 / 128 : ℝ) ≤ 1 + v := by linarith
    calc
      1 / (1 + v) ≤ 1 / (255 / 128 : ℝ) :=
        one_div_le_one_div_of_le
          (by norm_num : (0 : ℝ) < 255 / 128) hdenLower
      _ = 128 / 255 := by norm_num
  have hratio :
      (1 - v) / (1 + v) ≤
        (128 / 255 : ℝ) ^ 2 * e := by
    calc
      (1 - v) / (1 + v) = (1 - v) * (1 / (1 + v)) := by
        simp only [div_eq_mul_inv, one_mul]
      _ ≤ (1 - v) * (128 / 255 : ℝ) :=
        mul_le_mul_of_nonneg_left hinvUpper hd0
      _ = (128 / 255 : ℝ) * (1 - v) := by ring
      _ ≤ (128 / 255 : ℝ) * ((128 / 255 : ℝ) * e) :=
        mul_le_mul_of_nonneg_left hdUpper (by norm_num)
      _ = (128 / 255 : ℝ) ^ 2 * e := by ring
  have hpLoss :
      1 / 4 - p ≤ (4096 / 65025 : ℝ) * e := by
    rw [hpFormula]
    calc
      (1 - v) / (4 * (1 + v)) =
          (1 / 4 : ℝ) * ((1 - v) / (1 + v)) := by
        field_simp [hplus.ne']
      _ ≤ (1 / 4 : ℝ) * ((128 / 255 : ℝ) ^ 2 * e) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = (4096 / 65025 : ℝ) * e := by ring
  have hgapUpper :
      lrDA7ChannelAHBase p - 16 * Real.log (4 / 3) ≤
        (7168 / 7225 : ℝ) * e := by
    have hscaled := mul_le_mul_of_nonneg_left hpLoss
      (by norm_num : (0 : ℝ) ≤ 63 / 4)
    nlinarith [hgapSlope]
  change 0 ≤ lrDA7ChannelAH (lrCertificateV point) -
      16 * Real.log (4 / 3) ∧
    lrDA7ChannelAH (lrCertificateV point) - 16 * Real.log (4 / 3) ≤
      (7168 / 7225 : ℝ) * lrCertificateE point
  rw [lrDA7ChannelAH_eq_base]
  constructor
  · apply sub_nonneg.mpr
    simpa [p, v] using sub_nonneg.mp hgapNonnegative
  · simpa [p, v, e] using hgapUpper

lemma lrOneToFour_channel_AH_gap_le_e
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7ChannelAHGap point ∧
      lrDA7ChannelAHGap point ≤ lrCertificateE point := by
  have hgap := lrOneToFour_channel_AH_gap_bounds
    hinterior hdeep hkFour
  have he0 : 0 ≤ lrCertificateE point := hinterior.2.1.1.le
  constructor
  · exact hgap.1
  · have hfactor : (7168 / 7225 : ℝ) ≤ 1 := by norm_num
    exact hgap.2.trans (by nlinarith)

lemma lrOneToFour_channel_beta_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7ChannelBeta point ∧
      lrDA7ChannelBeta point ≤
        (51 / 200 : ℝ) * lrCertificateE point := by
  let v := lrCertificateV point
  have hv := lrCertificateV_mem_Ioo hinterior
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hplusUpper : 1 + v ≤ 2 := by linarith [hv.2]
  have hlogOrder : Real.log (1 + v) ≤ Real.log 2 :=
    Real.log_le_log hplus hplusUpper
  have hratioPos : 0 < 2 / (1 + v) :=
    div_pos (by norm_num) hplus
  have hlogUpper := Real.log_le_sub_one_of_pos hratioPos
  have hlogRatio : Real.log (2 / (1 + v)) =
      Real.log 2 - Real.log (1 + v) :=
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hplus.ne'
  rw [hlogRatio] at hlogUpper
  have hratio : 2 / (1 + v) - 1 = lrDA7ChannelB point / 2 := by
    change 2 / (1 + v) - 1 = (4 / (1 + v) - 2) / 2
    field_simp [hplus.ne']
    ring
  rw [hratio] at hlogUpper
  have hb := lrOneToFour_channel_b_bounds hinterior hdeep hkFour
  change 0 ≤ Real.log 2 - Real.log (1 + v) ∧
    Real.log 2 - Real.log (1 + v) ≤
      (51 / 200 : ℝ) * lrCertificateE point
  constructor
  · linarith
  · nlinarith [hb.2]

lemma lrOneToFour_channel_beta_mul_x_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelBeta point * lrCertificateX point ≤
      (51 / 200 : ℝ) * lrCertificateE point := by
  have hbeta := lrOneToFour_channel_beta_bounds
    hinterior hdeep hkFour
  have hxLe : lrCertificateX point ≤ 1 := by
    exact sub_nonneg.mp (lrDA7_x_loss_bounds hinterior).1
  have hscaled := mul_le_mul_of_nonneg_left hxLe hbeta.1
  have hscaled' :
      lrDA7ChannelBeta point * lrCertificateX point ≤
        lrDA7ChannelBeta point := by simpa using hscaled
  exact hscaled'.trans hbeta.2

lemma lrOneToFour_channel_A_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    0 < lrDA7ChannelA point := by
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hL := lrDA7_log_scale_pos hsIoc
  unfold lrDA7ChannelA
  linarith [lrDA7IdealC_nonnegative]

lemma lrOneToFour_finiteAH_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hkFour : point.k ≤ 4) :
    lrDA7FiniteAH point ≤ 1 + 3 * Real.log 2 := by
  have hs := hinterior.1
  have hk : 0 < point.k := by
    have hePos : 0 < point.s * point.k := by
      simpa [lrCertificateE] using hinterior.2.1.1
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hePos) hs.1.le
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hfinite := lrDA7FiniteAH_le_idealAH hinterior
  have hideal := lrLowKIdealAH_le_one_add_log hk hchi
  have hargPos : 0 < 1 + point.k := by linarith
  have hargOrder : 1 + point.k ≤ 8 := by linarith
  have hlogOrder : Real.log (1 + point.k) ≤ Real.log 8 :=
    Real.log_le_log hargPos hargOrder
  have hlogEight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlogEight] at hlogOrder
  exact hfinite.trans (hideal.trans (by linarith))

lemma lrOneToFour_finiteT_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7FiniteT point ∧
      lrDA7FiniteT point ≤ Real.log (1 / point.s) + 7 / 5 := by
  let L := Real.log (1 / point.s)
  have hLBase := lrLowK_log_scale_ge_L0 hinterior
    (hdeep.1.trans (by norm_num))
  have hSevenLog : 7 * Real.log 2 ≤ L := by
    simpa [L, lrLowKIdealL0] using hLBase
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAHUpper := lrOneToFour_finiteAH_upper hinterior hkFour
  have hAHLower := lrDA7FiniteAH_ge_one hinterior
  have hlogTwo : 2 * Real.log 2 < (7 / 5 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  constructor
  · unfold lrDA7FiniteT
    dsimp [L] at hSevenLog hAHUpper ⊢
    nlinarith
  · unfold lrDA7FiniteT
    change Real.log (1 / point.s) + 2 * Real.log 2 + 1 -
        lrDA7FiniteAH point ≤ Real.log (1 / point.s) + 7 / 5
    nlinarith [hAHLower, hlogTwo]

lemma lrOneToFour_idealB_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 < lrDA7IdealB point := by
  have hk : 0 < point.k := hinterior.1.1.trans_le hdeep.2
  have hargPos : 0 < 1 + point.k := by linarith
  have hargOrder : 1 + point.k ≤ 8 := by linarith
  have hlogOrder : Real.log (1 + point.k) ≤ Real.log 8 :=
    Real.log_le_log hargPos hargOrder
  have hlogEight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlogEight] at hlogOrder
  have hLBase := lrLowK_log_scale_ge_L0 hinterior
    (hdeep.1.trans (by norm_num))
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrDA7IdealB lrLowKIdealBOffset
  unfold lrLowKIdealL0 at hLBase
  nlinarith

lemma lrOneToFour_finiteB_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7FiniteB point ∧
      lrDA7FiniteB point ≤
        Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256 := by
  have hinterval := lrDA7FiniteB_ideal_interval hinterior
  have hidealPos := lrOneToFour_idealB_pos
    hinterior hdeep hkFour
  have hidealUpper := lrOneToFour_idealB_upper hinterior hdeep
  have heUpper := lrOneToFour_channel_e_le_inv4096
    hinterior hdeep hkFour
  constructor
  · exact hidealPos.le.trans hinterval.1
  · nlinarith [hinterval.2, hidealUpper, heUpper]

lemma lrOneToFour_channel_Jbar_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelJBar point ≤
      Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256 := by
  have hB := lrOneToFour_finiteB_bounds hinterior hdeep hkFour
  have hxLe : lrCertificateX point ≤ 1 := by
    exact sub_nonneg.mp (lrDA7_x_loss_bounds hinterior).1
  have hBx := mul_le_mul_of_nonneg_left hxLe hB.1
  have hD0 := lrDeterminantD1_nonnegative hinterior
  unfold lrDA7ChannelJBar
  linarith

lemma lrOneToFour_channel_c0q_mul_finiteT_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelC0Q point * lrDA7FiniteT point ≤
      (Real.log (1 / point.s) + 7 / 5) /
        (3 * Real.log (1 / point.s)) := by
  let L := Real.log (1 / point.s)
  let H := lrDA7ChannelH point
  let R := lrCertificateR point
  let tbar := lrDA7FiniteT point
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hHLower : L ≤ H := by
    simpa [L, H] using
      lrDA7_channel_H_ge_log_scale_coefficient hinterior
  have hHPos : 0 < H := hLPos.trans_le hHLower
  have hRPos : 0 < R := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hRLe : R ≤ 1 := by
    dsimp [R]
    unfold lrCertificateR
    linarith [hinterior.1.1]
  have htBounds : 0 ≤ tbar ∧ tbar ≤ L + 7 / 5 := by
    simpa [tbar, L] using
      lrOneToFour_finiteT_bounds hinterior hdeep hkFour
  have hRt : R * tbar ≤ L + 7 / 5 := by
    have hscaled := mul_le_mul_of_nonneg_right hRLe htBounds.1
    nlinarith
  have hleft := mul_le_mul_of_nonneg_right hRt hLPos.le
  have hright := mul_le_mul_of_nonneg_left hHLower
    (by linarith : 0 ≤ L + 7 / 5)
  unfold lrDA7ChannelC0Q
  change R / (3 * H) * tbar ≤ (L + 7 / 5) / (3 * L)
  rw [div_mul_eq_mul_div,
    div_le_div_iff₀ (mul_pos (by norm_num) hHPos)
      (mul_pos (by norm_num) hLPos)]
  nlinarith

lemma lrOneToFour_channel_gap_over_A_mul_Jbar_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelAHGap point / lrDA7ChannelA point *
        lrDA7ChannelJBar point ≤
      lrCertificateE point / Real.log (1 / point.s) *
        (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) := by
  let L := Real.log (1 / point.s)
  let A := lrDA7ChannelA point
  let h := lrDA7ChannelAHGap point
  let e := lrCertificateE point
  let Bmax := L / 2 + 7 / 10 + 1 / 256
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hAPos : 0 < A := by
    simpa [A] using lrOneToFour_channel_A_pos hinterior hdeep
  have hALower : L ≤ A := by
    dsimp [L, A]
    unfold lrDA7ChannelA
    linarith [lrDA7IdealC_nonnegative]
  have hgap : 0 ≤ h ∧ h ≤ e := by
    simpa [h, e] using
      lrOneToFour_channel_AH_gap_le_e hinterior hdeep hkFour
  have he0 : 0 ≤ e := hinterior.2.1.1.le
  have hdiv0 : 0 ≤ h / A := div_nonneg hgap.1 hAPos.le
  have hdivUpper : h / A ≤ e / L := by
    rw [div_le_div_iff₀ hAPos hLPos]
    have hfirst := mul_le_mul_of_nonneg_right hgap.2 hLPos.le
    have hsecond := mul_le_mul_of_nonneg_left hALower he0
    nlinarith
  have hBmax0 : 0 ≤ Bmax := by
    dsimp [Bmax]
    linarith
  have hJ : lrDA7ChannelJBar point ≤ Bmax := by
    simpa [Bmax, L] using
      lrOneToFour_channel_Jbar_upper hinterior hdeep hkFour
  have hfirst := mul_le_mul_of_nonneg_left hJ hdiv0
  have hsecond := mul_le_mul_of_nonneg_right hdivUpper hBmax0
  simpa [h, A, e, L, Bmax] using hfirst.trans hsecond

lemma lrOneToFour_channel_compensation_bracket_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelBeta point * lrCertificateX point +
        lrDA7ChannelAHGap point / lrDA7ChannelA point *
          lrDA7ChannelJBar point ≤
      lrCertificateE point *
        (51 / 200 +
          (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) /
            Real.log (1 / point.s)) := by
  have hbeta := lrOneToFour_channel_beta_mul_x_upper
    hinterior hdeep hkFour
  have hgap := lrOneToFour_channel_gap_over_A_mul_Jbar_upper
    hinterior hdeep hkFour
  calc
    lrDA7ChannelBeta point * lrCertificateX point +
          lrDA7ChannelAHGap point / lrDA7ChannelA point *
            lrDA7ChannelJBar point ≤
        (51 / 200 : ℝ) * lrCertificateE point +
          lrCertificateE point / Real.log (1 / point.s) *
            (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) :=
      add_le_add hbeta hgap
    _ = lrCertificateE point *
        (51 / 200 +
          (Real.log (1 / point.s) / 2 + 7 / 10 + 1 / 256) /
            Real.log (1 / point.s)) := by ring

theorem lrOneToFour_channel_coefficient_payment_two_fifths
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
        lrDA7FiniteT point ≤
      (2 / 5 : ℝ) * lrCertificateE point := by
  let L := Real.log (1 / point.s)
  let e := lrCertificateE point
  let ct := lrDA7ChannelC0Q point * lrDA7FiniteT point
  let bracket := lrDA7ChannelBeta point * lrCertificateX point +
    lrDA7ChannelAHGap point / lrDA7ChannelA point *
      lrDA7ChannelJBar point
  let f1 := (L + 7 / 5) / (3 * L)
  let f2 := 51 / 200 + (L / 2 + 7 / 10 + 1 / 256) / L
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using
      And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
  have hLPos : 0 < L := by
    dsimp [L]
    exact lrDA7_log_scale_pos hsIoc
  have hLBase := lrLowK_log_scale_ge_L0 hinterior
    (hdeep.1.trans (by norm_num))
  have hLminus : lrDA7LMinus ≤ L := by
    have hwindow := lrDA7_log_window.1.le
    dsimp [L]
    unfold lrLowKIdealL0 at hLBase
    exact hwindow.trans hLBase
  have hAPos := lrOneToFour_channel_A_pos hinterior hdeep
  have hHLower : L ≤ lrDA7ChannelH point := by
    simpa [L] using lrDA7_channel_H_ge_log_scale_coefficient hinterior
  have hHPos : 0 < lrDA7ChannelH point := hLPos.trans_le hHLower
  have hexact := lrDA7_channel_compensation_exact hAPos.ne' hHPos.ne'
  have hct : ct ≤ f1 := by
    simpa [ct, f1, L] using
      lrOneToFour_channel_c0q_mul_finiteT_upper
        hinterior hdeep hkFour
  have ht0 := (lrOneToFour_finiteT_bounds
    hinterior hdeep hkFour).1
  have hRPos : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hcq0 : 0 ≤ lrDA7ChannelC0Q point := by
    unfold lrDA7ChannelC0Q
    exact div_nonneg hRPos.le (mul_nonneg (by norm_num) hHPos.le)
  have hct0 : 0 ≤ ct := by
    dsimp [ct]
    exact mul_nonneg hcq0 ht0
  have hbracket : bracket ≤ e * f2 := by
    simpa [bracket, e, f2, L] using
      lrOneToFour_channel_compensation_bracket_upper
        hinterior hdeep hkFour
  have he0 : 0 ≤ e := hinterior.2.1.1.le
  have hf1Pos : 0 < f1 := by
    dsimp [f1]
    exact div_pos (by linarith) (mul_pos (by norm_num) hLPos)
  have hf2Nonnegative : 0 ≤ f2 := by
    dsimp [f2]
    exact add_nonneg (by norm_num)
      (div_nonneg (by linarith) hLPos.le)
  have hef2 : 0 ≤ e * f2 := mul_nonneg he0 hf2Nonnegative
  have hfirst : ct * bracket ≤ ct * (e * f2) :=
    mul_le_mul_of_nonneg_left hbracket hct0
  have hsecond : ct * (e * f2) ≤ f1 * (e * f2) :=
    mul_le_mul_of_nonneg_right hct hef2
  have hfactor := lrDA7_coefficient_scalar_factor_le_two_fifths hLminus
  calc
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
          lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
          lrDA7FiniteT point = ct * bracket := by
        rw [hexact]
        dsimp [ct, bracket]
        ring
    _ ≤ e * (f1 * f2) := by
      calc
        ct * bracket ≤ ct * (e * f2) := hfirst
        _ ≤ f1 * (e * f2) := hsecond
        _ = e * (f1 * f2) := by ring
    _ ≤ e * (2 / 5) :=
      mul_le_mul_of_nonneg_left
        (by simpa [f1, f2, L] using hfactor) he0
    _ = (2 / 5 : ℝ) * lrCertificateE point := by
      dsimp [e]
      ring

theorem lrOneToFour_channel_coefficient_payment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    (lrDA7FiniteC point * lrDA7ChannelJBar point -
        lrDA7ChannelC0Q point * lrDA7ChannelJ1 point) *
        lrDA7FiniteT point ≤
      lrBoundedDeepChannelCoefficientLoss point := by
  have h := lrOneToFour_channel_coefficient_payment_two_fifths
    hinterior hdeep hkFour
  unfold lrBoundedDeepChannelCoefficientLoss
  nlinarith [hinterior.2.1.1]

/-! ## Packaging and the low-channel endpoint -/

/-- All four true-channel payments required by the bounded-deep collector,
on the only band used by the restricted final assembly. -/
theorem lrOneToFour_trueChannelPayments
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    LRBoundedDeepTrueChannelPayments point
      (lrBoundedDeepLowDeltaGLoss point) :=
  { normalization_ne := (lrLowKNormalization_pos hinterior).ne'
    B_le_frozen := lrCertificateBFlow_le_lrDA7FiniteB hinterior
    frozenS_nonpos :=
      lrOneToFour_finiteS_nonpos hinterior hdeep hkFour
    deltaG := lrOneToFour_channel_deltaG_payment
      hinterior hdeep hkFour
    deltaOmega := lrOneToFour_channel_deltaOmega_payment
      hinterior hdeep hkFour
    deltaT := lrOneToFour_channel_deltaT_payment
      hinterior hrelevant hdeep hkFour
    coefficient := lrOneToFour_channel_coefficient_payment
      hinterior hdeep hkFour }

lemma lrOneToFour_s_mul_log_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    point.s * Real.log (1 / point.s) ≤
      (1 / 2 ^ 14 : ℝ) * (49 / 5) := by
  let s0 : ℝ := 1 / 2 ^ 14
  have hs0 : 0 < s0 := by norm_num [s0]
  have hendpointLog : Real.log (1 / s0) = 14 * Real.log 2 := by
    dsimp [s0]
    rw [show (1 / (1 / 2 ^ 14 : ℝ)) = 2 ^ 14 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (1 / s0) := by
    rw [hendpointLog]
    nlinarith [Real.log_two_gt_d9]
  have hsUpper : point.s ≤ s0 := by
    convert hdeep.1 using 1 <;> norm_num [s0]
  have hmul := lrDA7_mul_log_inv_le_endpoint
    hinterior.1.1 hs0 hsUpper hendpointOne
  have hendpointUpper : Real.log (1 / s0) ≤ (49 / 5 : ℝ) := by
    rw [hendpointLog]
    nlinarith [Real.log_two_lt_d9]
  have hscaled := mul_le_mul_of_nonneg_left hendpointUpper hs0.le
  exact hmul.trans (by simpa [s0] using hscaled)

/-- The exact low-channel endpoint appearing in the audited bounded-deep
budget.  The proof uses the conservative endpoint `e ≤ 2^-10`; the actual
restricted band gives the stronger `e ≤ 2^-12`. -/
theorem lrOneToFour_channelPointwiseLoss_le_lowEndpoint
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrBoundedDeepChannelPointwiseLoss point
        (lrBoundedDeepLowDeltaGLoss point) ≤
      lrBoundedDeepLowChannelEndpoint := by
  let e := lrCertificateE point
  let L := Real.log (1 / point.s)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
      simpa [lrDA7S0] using
        And.intro hinterior.1.1 (hdeep.1.trans (by norm_num))
    exact (lrDA7_log_scale_pos hsIoc).le
  have heFour : e ≤ 4 * point.s := by
    simpa [e] using lrOneToFour_channel_e_le_four_s hinterior hkFour
  have heUpper : e ≤ (1 / 2 ^ 12 : ℝ) := by
    change lrCertificateE point ≤ (1 / 2 ^ 12 : ℝ)
    convert lrOneToFour_channel_e_le_inv4096
      hinterior hdeep hkFour using 1 <;> norm_num
  have hsLog := lrOneToFour_s_mul_log_upper hinterior hdeep
  have heLog : e * L ≤ (1 / 2 ^ 10 : ℝ) * (49 / 5) := by
    have hscaled := mul_le_mul_of_nonneg_right heFour hL0
    calc
      e * L ≤ (4 * point.s) * L := hscaled
      _ = 4 * (point.s * L) := by ring
      _ ≤ 4 * ((1 / 2 ^ 14 : ℝ) * (49 / 5)) :=
        mul_le_mul_of_nonneg_left
          (by simpa [L] using hsLog) (by norm_num)
      _ ≤ (1 / 2 ^ 10 : ℝ) * (49 / 5) := by norm_num
  have heS : e * point.s ≤
      (1 / 2 ^ 10 : ℝ) * (1 / 2 ^ 14) := by
    have heLoose : e ≤ (1 / 2 ^ 10 : ℝ) :=
      heUpper.trans (by norm_num)
    have hsUpper : point.s ≤ (1 / 2 ^ 14 : ℝ) := by
      convert hdeep.1 using 1 <;> norm_num
    exact mul_le_mul heLoose hsUpper hinterior.1.1.le (by positivity)
  have hsLog' : point.s * L ≤
      (1 / 2 ^ 14 : ℝ) * (49 / 5) := by
    simpa [L] using hsLog
  have hdeltaG : lrBoundedDeepLowDeltaGLoss point ≤
      (51 / 50 : ℝ) * (1 / 2 ^ 10) *
        (49 / 5 + 1 / 2 ^ 14) := by
    unfold lrBoundedDeepLowDeltaGLoss
    dsimp [e, L] at heLog heS ⊢
    nlinarith
  have hdeltaOmega : lrBoundedDeepDeltaOmegaLoss point ≤
      (51 / 100 : ℝ) * (1 / 2 ^ 14) *
        (49 / 5 + 4 / 5) := by
    unfold lrBoundedDeepDeltaOmegaLoss
    dsimp [L] at hsLog' ⊢
    nlinarith [hdeep.1]
  have heUpper' :
      lrCertificateE point ≤ (1 / 2 ^ 12 : ℝ) := by
    simpa [e] using heUpper
  have hdeltaT : lrBoundedDeepDeltaTLoss point ≤ 1 / 10240 := by
    unfold lrBoundedDeepDeltaTLoss
    nlinarith [heUpper']
  have hcoefficient : lrBoundedDeepChannelCoefficientLoss point ≤
      3 / 5120 := by
    unfold lrBoundedDeepChannelCoefficientLoss
    nlinarith [heUpper']
  unfold lrBoundedDeepChannelPointwiseLoss
    lrBoundedDeepLowChannelEndpoint
  linarith

theorem lrOneToFour_trueChannel_loss_le_lowEndpoint
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7FiniteFrozenCore point - lrDA7TrueChannelCore point ≤
      lrBoundedDeepLowChannelEndpoint := by
  exact (lrBoundedDeep_trueChannel_loss
    (lrOneToFour_trueChannelPayments
      hinterior hrelevant hdeep hkFour)).trans
    (lrOneToFour_channelPointwiseLoss_le_lowEndpoint
      hinterior hdeep hkFour)

end CourtadeKumar
