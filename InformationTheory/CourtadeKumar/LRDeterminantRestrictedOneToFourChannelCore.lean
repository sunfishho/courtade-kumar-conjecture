import InformationTheory.CourtadeKumar.LRDeterminantRestrictedOneToFourChannelPhysical

/-!
# Restricted true-channel core bounds

This is the second standalone checkpoint for the restricted true-channel
restoration.  It transports the checked physical endpoint bound for `v` into
the three reusable estimates for `d = 1-v`, the channel coefficient `B`, and
the radial coefficient `kappa`.
-/

namespace CourtadeKumar

lemma lrOneToFour_channel_d_le
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelD point ≤ (128 / 255 : ℝ) * lrCertificateE point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using
      lrOneToFour_channel_v_lower hinterior hdeep hkFour
  have hd : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := calc
      point.chi * lrCertificateE point < 1 * lrCertificateE point :=
        mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
      _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hradPos : 0 < (1 - e) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvSq : v ^ 2 = (1 - e) / lrCertificateX point := by
    dsimp [v]
    unfold lrCertificateV
    exact Real.sq_sqrt hradPos.le
  have hxLe : lrCertificateX point ≤ 1 := by
    unfold lrCertificateX
    exact sub_le_self _
      (mul_nonneg hinterior.2.2.1.le hinterior.2.1.1.le)
  have hnumLeSq : 1 - e ≤ v ^ 2 := by
    rw [hvSq, le_div_iff₀ hxPos]
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2.le)
      (sub_nonneg.mpr hxLe)]
  have hsqLoss : 1 - v ^ 2 ≤ e := by linarith
  have hfactor : (1 - v) * (1 + v) = 1 - v ^ 2 := by ring
  have hfactorLower : (255 / 128 : ℝ) ≤ 1 + v := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hfactorLower hd
  change 1 - v ≤ (128 / 255 : ℝ) * e
  nlinarith [hscaled, hfactor, hsqLoss]

lemma lrOneToFour_channel_b_bounds
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 ≤ lrDA7ChannelB point ∧
      lrDA7ChannelB point ≤
        (51 / 100 : ℝ) * lrCertificateE point := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using
      lrOneToFour_channel_v_lower hinterior hdeep hkFour
  have hd : 0 ≤ 1 - v := sub_nonneg.mpr hv.2.le
  have hdUpper : 1 - v ≤ (128 / 255 : ℝ) * e := by
    simpa [lrDA7ChannelD, e, v] using
      lrOneToFour_channel_d_le hinterior hdeep hkFour
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hbEq : lrDA7ChannelB point = 2 * (1 - v) / (1 + v) := by
    change 4 / (1 + v) - 2 = 2 * (1 - v) / (1 + v)
    field_simp [hden.ne']
    ring
  rw [hbEq]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hd) hden.le
  · rw [div_le_iff₀ hden]
    have hfactor : (255 / 128 : ℝ) ≤ 1 + v := by linarith
    have hfactorScaled := mul_le_mul_of_nonneg_left hfactor he.1.le
    dsimp [e] at hdUpper hfactorScaled ⊢
    nlinarith

lemma lrOneToFour_channel_kappa_le_seventh
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7ChannelKappa point ≤ lrCertificateE point ^ 2 / 7 := by
  let e := lrCertificateE point
  let v := lrCertificateV point
  let d := 1 - v
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvLower : (127 / 128 : ℝ) ≤ v := by
    simpa [v] using
      lrOneToFour_channel_v_lower hinterior hdeep hkFour
  have hd0 : 0 ≤ d := by dsimp [d]; linarith [hv.2]
  have hdUpper : d ≤ (128 / 255 : ℝ) * e := by
    simpa [d, e, v, lrDA7ChannelD] using
      lrOneToFour_channel_d_le hinterior hdeep hkFour
  have hscaled : 255 * d ≤ 128 * e := by nlinarith
  have hscaled0 : 0 ≤ 255 * d := mul_nonneg (by norm_num) hd0
  have hsquare := mul_self_le_mul_self hscaled0 hscaled
  have hdsq : d ^ 2 ≤ (128 / 255 : ℝ) ^ 2 * e ^ 2 := by
    nlinarith
  have hdenLower :
      (127 / 128 : ℝ) * (255 / 128) ≤ v * (1 + v) := by
    exact mul_le_mul hvLower (by linarith : (255 / 128 : ℝ) ≤ 1 + v)
      (by norm_num) hv.1.le
  have hconstant :
      7 * (128 / 255 : ℝ) ^ 2 ≤
        (127 / 128 : ℝ) * (255 / 128) := by
    norm_num
  have hleft := mul_le_mul_of_nonneg_left hdsq
    (by norm_num : (0 : ℝ) ≤ 7)
  have hconstantScaled :=
    mul_le_mul_of_nonneg_right hconstant (sq_nonneg e)
  have hdenScaled :=
    mul_le_mul_of_nonneg_left hdenLower (sq_nonneg e)
  have hnum : 7 * d ^ 2 ≤ e ^ 2 * (v * (1 + v)) := by
    calc
      7 * d ^ 2 ≤
          (7 * (128 / 255 : ℝ) ^ 2) * e ^ 2 := by
        nlinarith [hleft]
      _ ≤ ((127 / 128 : ℝ) * (255 / 128)) * e ^ 2 :=
        hconstantScaled
      _ ≤ e ^ 2 * (v * (1 + v)) := by
        nlinarith [hdenScaled]
  have hdenPos : 0 < v * (1 + v) :=
    mul_pos hv.1 (by linarith [hv.1])
  unfold lrDA7ChannelKappa
  change d ^ 2 / (v * (1 + v)) ≤ e ^ 2 / 7
  rw [div_le_div_iff₀ hdenPos (by norm_num : (0 : ℝ) < 7)]
  nlinarith [hnum]

end CourtadeKumar
