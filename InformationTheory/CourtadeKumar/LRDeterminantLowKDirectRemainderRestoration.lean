import InformationTheory.CourtadeKumar.LRDeterminantBoundedDeepRestoration

/-!
# Direct entropy-remainder restoration on the determinant low-`k` row

This module proves the post-channel direct `Q = q + r` restoration payment.
It establishes the two remainder-coordinate signs analytically, collects them
through the exact bounded-deep decomposition, and pays the sole adverse
`Omega_r` term against the audited `lrDA7DirectEndpoint`.

The final adapter shows that, after this theorem and the already-proved true
channel stage, `LRLowKRemainingRestoration` depends only on the separate
entropy/coefficient comparison.
-/

open Set

namespace CourtadeKumar

/-! ## Signs for the direct entropy remainder -/

lemma lrLowK_r0_monotoneOn_Ico :
    MonotoneOn lrLowerFaceR0 (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico (0 : ℝ) 1)
  · intro y hy
    rcases hy.1.eq_or_lt with rfl | hyPos
    · exact continuousWithinAt_lrLowerFaceR0_zero
    · exact (hasDerivAt_lrLowerFaceR0 ⟨hyPos, hy.2⟩).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ico] at hy
    exact (hasDerivAt_lrLowerFaceR0 hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ico] at hy
    rw [(hasDerivAt_lrLowerFaceR0 hy).deriv]
    exact lrLowerFaceR0Prime_nonneg hy

lemma lrBoundedDeep_RGap_nonnegative_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrBoundedDeepRGap point := by
  let s := point.s
  let e := lrCertificateE point
  let y0 := lrCertificateY0 point
  let v := lrCertificateV point
  let rS := lrLowerFaceR0 s
  let rY := lrLowerFaceR0 (lrCertificateB s y0)
  let rE := lrLowerFaceR0 (lrCertificateB s e)
  have hs := hinterior.1
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hy0 : y0 ∈ Ioo (0 : ℝ) 1 := by
    dsimp [y0]
    unfold lrCertificateY0
    constructor
    · exact mul_pos hinterior.2.2.1 he.1
    · have hmul := mul_lt_mul_of_pos_right hinterior.2.2.2 he.1
      nlinarith [hmul, he.2]
  have hby := lrCertificateB_mem_Ioo hs hy0
  have hbe := lrCertificateB_mem_Ioo hs he
  have hsMem : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  have hbyMem : lrCertificateB s y0 ∈ Ico (0 : ℝ) 1 :=
    ⟨hby.1.le, hby.2⟩
  have hbeMem : lrCertificateB s e ∈ Ico (0 : ℝ) 1 :=
    ⟨hbe.1.le, hbe.2⟩
  have hsy : s ≤ lrCertificateB s y0 := by
    unfold lrCertificateB
    dsimp [s]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) hy0.1.le]
  have hse : s ≤ lrCertificateB s e := by
    unfold lrCertificateB
    dsimp [s]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) he.1.le]
  have hrY : rS ≤ rY := by
    dsimp [rS, rY]
    exact lrLowK_r0_monotoneOn_Ico hsMem hbyMem hsy
  have hrE : rS ≤ rE := by
    dsimp [rS, rE]
    exact lrLowK_r0_monotoneOn_Ico hsMem hbeMem hse
  have hrS0 : 0 ≤ rS := by
    dsimp [rS, s]
    exact lrLowerFaceR0_nonneg hs
  have hrEDiv : rS / v ≤ rE / v :=
    div_le_div_of_nonneg_right hrE hv.1.le
  have hsum : (1 + 1 / v) * rS ≤ rY + rE / v := by
    have := add_le_add hrY hrEDiv
    field_simp [hv.1.ne'] at this ⊢
    nlinarith
  have hkappa0 : 0 ≤ lrDA7ChannelKappa point :=
    lrDA7_channel_kappa_nonnegative hinterior
  have hcoeff :
      1 + 1 / v - 4 / (1 + v) = lrDA7ChannelKappa point := by
    dsimp [v]
    unfold lrDA7ChannelKappa lrDA7ChannelD
    field_simp [hv.1.ne', (by linarith [hv.1] : 1 + lrCertificateV point ≠ 0)]
    ring
  have hcoeffR :
      4 / (1 + v) * rS ≤ (1 + 1 / v) * rS := by
    have hscaled := mul_nonneg hkappa0 hrS0
    rw [← hcoeff] at hscaled
    nlinarith
  have hcoeffR' :
      4 * rS / (1 + v) ≤ (1 + 1 / v) * rS := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hcoeffR
  have htarget :
      4 * rS / (1 + v) ≤ rY + rE / v :=
    hcoeffR'.trans hsum
  unfold lrBoundedDeepRGap lrBoundedDeepRSquareTarget
    lrBoundedDeepRPrefixAtM
  dsimp [s, e, y0, v, rS, rY, rE] at htarget ⊢
  linarith

lemma lrBoundedDeep_ROmega_lower_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    -lrDA7ChannelKappa point * point.s *
        lrLowerFaceR0Prime point.s ≤
      lrBoundedDeepROmega point := by
  let v := lrCertificateV point
  let w := lrLowerFaceOmegaR0 point.s 0
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := hinterior.1
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hy0 : lrCertificateY0 point ∈ Ico (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_nonneg hchi.1 he.1.le
    · exact (mul_le_of_le_one_left he.1.le hchi.2).trans_lt he.2
  have hmono := lrLowerFaceOmegaR0_monotoneOn_Ico hs
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hY := hmono hzero hy0 hy0.1
  have hE := hmono hzero
    (show lrCertificateE point ∈ Ico (0 : ℝ) 1 from ⟨he.1.le, he.2⟩)
    he.1.le
  have hEDiv : w / v ≤
      lrLowerFaceOmegaR0 point.s (lrCertificateE point) / v := by
    exact div_le_div_of_nonneg_right (by simpa [w] using hE) hv.1.le
  have hPW : (1 + 1 / v) * w ≤ lrBoundedDeepRPW point := by
    unfold lrBoundedDeepRPW lrLowerFacePWR0
    have hadd := add_le_add (by simpa [w] using hY) hEDiv
    convert hadd using 1
    field_simp [hv.1.ne']
    ring
  have hcoeff :
      1 + 1 / v - 4 / (1 + v) = lrDA7ChannelKappa point := by
    dsimp [v]
    unfold lrDA7ChannelKappa lrDA7ChannelD
    field_simp [hv.1.ne', (by linarith [hv.1] : 1 + lrCertificateV point ≠ 0)]
    ring
  have hOmegaBase : lrDA7ChannelKappa point * w ≤
      lrBoundedDeepROmega point := by
    calc
      lrDA7ChannelKappa point * w =
          (1 + 1 / v) * w - 4 * w / (1 + v) := by
            rw [← hcoeff]
            ring
      _ ≤ lrBoundedDeepRPW point - 4 * w / (1 + v) :=
        sub_le_sub_right hPW _
      _ = lrBoundedDeepROmega point := by
        unfold lrBoundedDeepROmega lrBoundedDeepRW
        simp only [v, w]
  have hwLower := lrLowerFaceOmegaR0_zero_lower hs
  have hk0 := lrDA7_channel_kappa_nonnegative hinterior
  have hscaled := mul_le_mul_of_nonneg_left hwLower hk0
  have hlower :
      -lrDA7ChannelKappa point * point.s *
          lrLowerFaceR0Prime point.s ≤
        lrDA7ChannelKappa point * w := by
    calc
      -lrDA7ChannelKappa point * point.s * lrLowerFaceR0Prime point.s =
          lrDA7ChannelKappa point *
            (-point.s * lrLowerFaceR0Prime point.s) := by ring
      _ ≤ lrDA7ChannelKappa point * w := hscaled
  exact hlower.trans hOmegaBase

lemma lrBoundedDeep_directRemainderSigns_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point) :
    LRBoundedDeepDirectRemainderSigns point := by
  have hn := lrLowKNormalization_pos hinterior
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hD := lrDeterminantD1_nonnegative hinterior
  have hB := (lrCertificateBFlow_pos hinterior).le
  have hW := (lrCertificateW_pos hinterior).le
  have hHd := lrDeterminantHd_pos hinterior
  have hc0 := lrDeterminantC0_nonnegative hinterior.1.1 hHd hR.le hW
  have hJ := (lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant).le
  have hRG : 0 ≤ lrBoundedDeepRNormalizedG point := by
    unfold lrBoundedDeepRNormalizedG lrBoundedDeepRG
    exact div_nonneg (lrLowRatioR0G_nonnegative hinterior) hn.le
  have hROmega :
      -lrBoundedDeepDirectOmegaCost point ≤
        lrBoundedDeepRNormalizedOmega point := by
    have hraw := lrBoundedDeep_ROmega_lower_lowK hinterior
    unfold lrBoundedDeepDirectOmegaCost lrBoundedDeepRNormalizedOmega
    rw [show -(lrDA7ChannelKappa point * point.s *
          lrLowerFaceR0Prime point.s / lrLowKNormalization point) =
        (-lrDA7ChannelKappa point * point.s *
          lrLowerFaceR0Prime point.s) / lrLowKNormalization point by ring]
    exact (div_le_div_iff_of_pos_right hn).2 hraw
  have hRT : 0 ≤ lrBoundedDeepRNormalizedT point := by
    unfold lrBoundedDeepRNormalizedT
    exact div_nonneg (div_nonneg
      (lrBoundedDeep_RGap_nonnegative_lowK hinterior) hR.le) hn.le
  have hfavorable :
      0 ≤ 4 * lrDeterminantDelta point * lrCertificateBFlow point *
          lrCertificateW point / lrLowKNormalization point := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (lrDeterminantDelta_nonnegative hinterior))
          hB)
        hW)
      hn.le
  exact
    { d1_nonneg := hD
      d1_add_B_nonneg := add_nonneg hD hB
      c0J1_nonneg := mul_nonneg hc0 hJ
      rG_nonneg := hRG
      rOmega_lower := hROmega
      rT_nonneg := hRT
      favorable_nonneg := hfavorable }

/-! ## Direct endpoint envelope -/

lemma lrDA7_D1_add_BFlow_upper_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    lrDeterminantD1 point + lrCertificateBFlow point ≤
      Real.log (1 / point.s) + 4 / 5 := by
  let e := lrCertificateE point
  let L := Real.log (1 / point.s)
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hDleIdeal := (lrDeterminantD1_lowK_finite_bounds hinterior hregion).2
  have hIdealDUpper :=
    lrDA7IdealD_upper hinterior.1.1 hsIoc.2 hregion.2.1
  have hBTrue := lrCertificateBFlow_le_lrDA7FiniteB hinterior
  have hBFinite := (lrDA7FiniteB_ideal_interval hinterior).2
  have hBIdeal := lrDA7IdealB_upper hinterior hregion
  have heS : e ≤ point.s := by
    simpa [e] using lrDA7_channel_e_le_s hinterior hregion
  have hsUpper : point.s ≤ 1 / 128 := by
    simpa [lrDA7S0] using hsIoc.2
  dsimp [e, L] at hDleIdeal hIdealDUpper hBTrue hBFinite hBIdeal heS ⊢
  nlinarith [hsUpper]

noncomputable def lrDA7PDirWeight (s : ℝ) : ℝ :=
  s ^ 3 * lrDA7PDir (Real.log (1 / s))

lemma hasDerivAt_lrDA7PDirWeight
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt lrDA7PDirWeight
      (s ^ 2 *
        (3 * lrDA7PDir (Real.log (1 / s)) -
          lrDA7PDirPrime (Real.log (1 / s)))) s := by
  let L := Real.log (1 / s)
  have hL := hasDerivAt_lrDA7Log hs
  have hleft := hL.add_const (4 / 5)
  have hright := hL.add_const (7 / 5)
  have hcube : HasDerivAt (fun x : ℝ ↦ x ^ 3) (3 * s ^ 2) s := by
    simpa using (hasDerivAt_id s).pow 3
  have hprod := hcube.mul (hleft.mul hright)
  unfold lrDA7PDirWeight lrDA7PDir lrDA7PDirPrime
  convert hprod using 1
  simp only [Pi.mul_apply]
  field_simp [hs.ne']
  ring

lemma lrDA7PDirWeight_monotoneOn :
    MonotoneOn lrDA7PDirWeight (Ioc (0 : ℝ) lrDA7S0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) lrDA7S0)
  · intro s hs
    exact (hasDerivAt_lrDA7PDirWeight hs.1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact (hasDerivAt_lrDA7PDirWeight hs.1).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    rw [(hasDerivAt_lrDA7PDirWeight hs.1).deriv]
    exact mul_nonneg (sq_nonneg s)
      (lrDA7_endpoint_polynomial_gaps_pos
        (lrDA7_log_scale_ge_LMinus
          (show s ∈ Ioc (0 : ℝ) lrDA7S0 from ⟨hs.1, hs.2.le⟩))).2.1.le

lemma lrDA7PDir_endpoint_order :
    lrDA7PDir (7 * Real.log 2) ≤ lrDA7PDir lrDA7LPlus := by
  have horder := lrDA7_log_window.2.le
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum :
      0 ≤ lrDA7LPlus + 7 * Real.log 2 +
        (4 / 5 : ℝ) + 7 / 5 := by
    dsimp [lrDA7LPlus]
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr horder) hsum
  unfold lrDA7PDir
  nlinarith

lemma lrDA7_s_cube_mul_PDir_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    s ^ 3 * lrDA7PDir (Real.log (1 / s)) ≤
      lrDA7S0 ^ 3 * lrDA7PDir lrDA7LPlus := by
  have hmono := lrDA7PDirWeight_monotoneOn hs
    (show lrDA7S0 ∈ Ioc (0 : ℝ) lrDA7S0 by norm_num [lrDA7S0]) hs.2
  have hendpointLog :
      Real.log (1 / lrDA7S0) = 7 * Real.log 2 := by
    dsimp [lrDA7S0]
    rw [show (1 / (1 / 128 : ℝ)) = 2 ^ 7 by norm_num,
      Real.log_pow]
    norm_num
  unfold lrDA7PDirWeight at hmono
  rw [hendpointLog] at hmono
  have hscaled := mul_le_mul_of_nonneg_left lrDA7PDir_endpoint_order
    (pow_nonneg (show 0 ≤ lrDA7S0 by norm_num [lrDA7S0]) 3)
  exact hmono.trans hscaled

lemma lrDA7_direct_pointwise_le_endpoint
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) lrDA7S0) :
    (3 / 14 : ℝ) * s ^ 3 *
        lrDA7PDir (Real.log (1 / s)) ≤
      lrDA7DirectEndpoint := by
  have h := lrDA7_s_cube_mul_PDir_upper hs
  have hscaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3 / 14)
  unfold lrDA7DirectEndpoint lrDA7PDir
  simpa [mul_assoc] using hscaled

lemma lrBoundedDeep_directOmegaCost_pointwise_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowKRegion point) :
    (lrDeterminantD1 point + lrCertificateBFlow point) *
        lrBoundedDeepDirectOmegaCost point ≤
      (3 / 14 : ℝ) * point.s ^ 3 *
        lrDA7PDir (Real.log (1 / point.s)) := by
  let e := lrCertificateE point
  let n := lrLowKNormalization point
  let A := lrDeterminantD1 point + lrCertificateBFlow point
  let kappa := lrDA7ChannelKappa point
  let rp := lrLowerFaceR0Prime point.s
  let L := Real.log (1 / point.s)
  have hsIoc : point.s ∈ Ioc (0 : ℝ) lrDA7S0 := by
    simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1
  have hs16 : point.s ∈ Ioo (0 : ℝ) (1 / 16) :=
    ⟨hinterior.1.1, hregion.1.trans_lt (by norm_num)⟩
  have he := hinterior.2.1
  have heS : e ≤ point.s := by
    simpa [e] using lrDA7_channel_e_le_s hinterior hregion
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
    simpa [A, L] using lrDA7_D1_add_BFlow_upper_lowK hinterior hregion
  have hk0 : 0 ≤ kappa := by
    simpa [kappa] using lrDA7_channel_kappa_nonnegative hinterior
  have hk : kappa ≤ e ^ 2 / 7 := by
    simpa [kappa, e] using lrDA7_channel_kappa_le_seventh hinterior hregion
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
      nlinarith [Real.log_two_lt_d9]
    have hsThird : 0 ≤ point.s / 3 :=
      div_nonneg hinterior.1.1.le (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left
      (add_le_add_left hlogTwo L) hsThird
    have hscaled' :
        point.s / 3 * (L + 2 * Real.log 2) ≤
          point.s / 3 * (L + 7 / 5) := by
      simpa [add_comm] using hscaled
    simpa [rp] using hrpRaw.trans hscaled'
  have hL0 : 0 ≤ L := (lrDA7_log_scale_pos hsIoc).le
  have hP0 : 0 ≤ lrDA7PDir L := by
    unfold lrDA7PDir
    positivity
  have hcostCleared :
      A * kappa * point.s * rp ≤
        ((3 / 14 : ℝ) * point.s ^ 3 * lrDA7PDir L) * n := by
    have hAk : A * kappa ≤ (L + 4 / 5) * (e ^ 2 / 7) :=
      mul_le_mul hA hk hk0 (by linarith)
    have hAks := mul_le_mul_of_nonneg_right hAk hinterior.1.1.le
    have hAks0 : 0 ≤ A * kappa * point.s :=
      mul_nonneg (mul_nonneg hA0 hk0) hinterior.1.1.le
    have hAksUpper0 :
        0 ≤ ((L + 4 / 5) * (e ^ 2 / 7)) * point.s :=
      mul_nonneg
        (mul_nonneg (by linarith) (div_nonneg (sq_nonneg e) (by norm_num)))
        hinterior.1.1.le
    have hrpBound0 : 0 ≤ point.s / 3 * (L + 7 / 5) :=
      mul_nonneg (div_nonneg hinterior.1.1.le (by norm_num)) (by linarith)
    have hleft := mul_le_mul hAks hrp hrp0 hAksUpper0
    have hleft' :
        A * kappa * point.s * rp ≤
          e ^ 2 * point.s ^ 2 / 21 * lrDA7PDir L := by
      calc
        A * kappa * point.s * rp ≤
            ((L + 4 / 5) * (e ^ 2 / 7)) * point.s *
              (point.s / 3 * (L + 7 / 5)) := hleft
        _ = e ^ 2 * point.s ^ 2 / 21 * lrDA7PDir L := by
          unfold lrDA7PDir
          ring
    have heSq : e ^ 2 ≤ e * point.s := by
      nlinarith [mul_nonneg he.1.le (sub_nonneg.mpr heS)]
    have hfactor0 : 0 ≤ point.s ^ 2 / 21 * lrDA7PDir L := by positivity
    have heStep := mul_le_mul_of_nonneg_right heSq hfactor0
    have hnStep := mul_le_mul_of_nonneg_left hnLower
      (show 0 ≤ (3 / 14 : ℝ) * point.s ^ 3 * lrDA7PDir L by
        exact mul_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg hinterior.1.1.le 3)) hP0)
    calc
      A * kappa * point.s * rp ≤
          e ^ 2 * point.s ^ 2 / 21 * lrDA7PDir L := hleft'
      _ ≤ e * point.s * (point.s ^ 2 / 21 * lrDA7PDir L) := by
        nlinarith [heStep]
      _ ≤ ((3 / 14 : ℝ) * point.s ^ 3 * lrDA7PDir L) * (e / 4) := by
        have hnonneg : 0 ≤ e * point.s ^ 3 * lrDA7PDir L :=
          mul_nonneg (mul_nonneg he.1.le (pow_nonneg hinterior.1.1.le 3)) hP0
        nlinarith
      _ ≤ ((3 / 14 : ℝ) * point.s ^ 3 * lrDA7PDir L) * n := hnStep
  unfold lrBoundedDeepDirectOmegaCost
  dsimp [A, kappa, rp, n, L] at hcostCleared ⊢
  calc
    (lrDeterminantD1 point + lrCertificateBFlow point) *
          (lrDA7ChannelKappa point * point.s *
            lrLowerFaceR0Prime point.s / lrLowKNormalization point) =
        ((lrDeterminantD1 point + lrCertificateBFlow point) *
          lrDA7ChannelKappa point * point.s *
            lrLowerFaceR0Prime point.s) / lrLowKNormalization point := by ring
    _ ≤ (3 / 14 : ℝ) * point.s ^ 3 *
          lrDA7PDir (Real.log (1 / point.s)) :=
      (div_le_iff₀ hnPos).2 hcostCleared

theorem lrBoundedDeep_direct_remainder_stage_proved_lowK
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point) :
    lrBoundedDeepActualCoefficientQCore point - lrDA7DirectEndpoint ≤
      lrLowKActualNormalized point := by
  have hsigns := lrBoundedDeep_directRemainderSigns_lowK hinterior hrelevant
  have hraw := lrBoundedDeep_qCore_sub_actual_le_directCost
    (lrLowKNormalization_pos hinterior).ne'
    (lrBoundedDeep_qChannelIdentification hinterior) hsigns
  have hpoint := lrBoundedDeep_directOmegaCost_pointwise_lowK hinterior hregion
  have hendpoint := lrDA7_direct_pointwise_le_endpoint
    (show point.s ∈ Ioc (0 : ℝ) lrDA7S0 by
      simpa [lrDA7S0] using And.intro hinterior.1.1 hregion.1)
  linarith

/-! Once the direct theorem above is available, the complete low-`k`
post-channel interface has only the entropy/coefficient comparison left. -/

noncomputable def lrLowKRemainingRestoration_of_entropyCoefficient
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantLowKRegion point)
    (hentropy :
      lrDA7TrueChannelCore point -
          lrBoundedDeepActualCoefficientQCore point ≤
        lrDA7EntropyEndpoint) :
    LRLowKRemainingRestoration point := by
  refine
    { afterChannel := lrDA7TrueChannelCore point
      afterEntropyCoefficient := lrBoundedDeepActualCoefficientQCore point
      channel := lrDA7_true_channel_stage_proved hinterior hrelevant hregion
      entropyCoefficient := ?_
      directRemainder := ?_ }
  · linarith
  · exact lrBoundedDeep_direct_remainder_stage_proved_lowK
      hinterior hrelevant hregion

end CourtadeKumar
