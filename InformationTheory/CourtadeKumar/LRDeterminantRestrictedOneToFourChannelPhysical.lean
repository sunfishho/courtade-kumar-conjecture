import InformationTheory.CourtadeKumar.LRDeterminantBoundedDeepRestoration

/-!
# Minimal restricted true-channel physical checkpoint

This module isolates the first new ingredients: `e = s*k ≤ 4s ≤ 2^-12`,
the resulting old-style channel endpoint `127/128 ≤ v`, and the global sign
of the finite frozen angular coordinate.  The full true-channel restoration
imports this checkpoint, so each frontier argument is checked once in a small
module.
-/

open Set

namespace CourtadeKumar

lemma lrOneToFour_channel_e_le_four_s
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hkFour : point.k ≤ 4) :
    lrCertificateE point ≤ 4 * point.s := by
  unfold lrCertificateE
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hkFour hinterior.1.1.le)

lemma lrOneToFour_channel_e_le_inv4096
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrCertificateE point ≤ 1 / 4096 := by
  have heFour := lrOneToFour_channel_e_le_four_s hinterior hkFour
  nlinarith [hdeep.1]

lemma lrOneToFour_channel_e_lt_one
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrCertificateE point < 1 := by
  have he := lrOneToFour_channel_e_le_inv4096 hinterior hdeep hkFour
  linarith

/-- The restricted deep channel is much shorter than the old low-`k`
channel; the old convenient endpoint `127/128` remains available. -/
lemma lrOneToFour_channel_v_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    (127 / 128 : ℝ) ≤ lrCertificateV point := by
  let e := lrCertificateE point
  let x := lrCertificateX point
  let v := lrCertificateV point
  have he := hinterior.2.1
  have hxPos : 0 < x := by
    dsimp [x]
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := calc
      point.chi * lrCertificateE point < 1 * lrCertificateE point :=
        mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
      _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hxLe : x ≤ 1 := by
    dsimp [x]
    unfold lrCertificateX
    exact sub_le_self _
      (mul_nonneg hinterior.2.2.1.le hinterior.2.1.1.le)
  have hradPos : 0 < (1 - e) / x :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvSq : v ^ 2 = (1 - e) / x := by
    dsimp [v]
    unfold lrCertificateV
    exact Real.sq_sqrt hradPos.le
  have hnumLeSq : 1 - e ≤ v ^ 2 := by
    rw [hvSq, le_div_iff₀ hxPos]
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2.le)
      (sub_nonneg.mpr hxLe)]
  have heUpper : e ≤ 1 / 128 := by
    dsimp [e]
    exact (lrOneToFour_channel_e_le_inv4096
      hinterior hdeep hkFour).trans (by norm_num)
  have hvSqLower : (127 / 128 : ℝ) ≤ v ^ 2 := by
    nlinarith
  have hv := lrCertificateV_mem_Ioo hinterior
  by_contra hnot
  have hvLt : v < 127 / 128 := lt_of_not_ge hnot
  have hvSqLt : v ^ 2 < (127 / 128 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hv.1.le (by norm_num)).2 hvLt
  norm_num at hvSqLower hvSqLt
  nlinarith

/-! ## The finite frozen angular sign -/

/-- The comparison needed for the finite frozen `S` coordinate is already a
consequence of physicality.  Neither the deep cutoff nor `k ≤ 4` is needed:
`s*k < 1` gives both logarithmic argument comparisons. -/
lemma lrOneToFour_log_k_add_qChi_le_finiteA
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    Real.log point.k + lrLowKIdealQChi point.chi ≤
      lrDA7FiniteA point := by
  have hk : 0 < point.k := lrBoundedDeep_k_pos hinterior
  have hchi := hinterior.2.2
  have heLt : point.s * point.k < 1 := by
    simpa [lrCertificateE] using hinterior.2.1.2
  have hechiLt : point.s * point.k * point.chi < 1 := by
    have hscaled := mul_lt_mul_of_pos_right heLt hchi.1
    have hscaled' : point.s * point.k * point.chi < point.chi := by
      simpa only [one_mul] using hscaled
    exact hscaled'.trans hchi.2
  have houterOrder :
      point.k ≤ 1 + (1 - point.s) * point.k := by
    nlinarith
  have hinnerOrder :
      point.k * point.chi ≤
        1 + (1 - point.s) * point.k * point.chi := by
    nlinarith
  have houterLog :
      Real.log point.k ≤
        Real.log (1 + (1 - point.s) * point.k) :=
    Real.log_le_log hk houterOrder
  have hkchi : 0 < point.k * point.chi := mul_pos hk hchi.1
  have hinnerLog :
      Real.log (point.k * point.chi) ≤
        Real.log (1 + (1 - point.s) * point.k * point.chi) :=
    Real.log_le_log hkchi hinnerOrder
  have hlogMul :
      Real.log (point.k * point.chi) =
        Real.log point.k + Real.log point.chi := by
    rw [Real.log_mul hk.ne' hchi.1.ne']
  rw [hlogMul] at hinnerLog
  have hweighted :=
    mul_le_mul_of_nonneg_left hinnerLog hchi.1.le
  have hden : 0 < 1 + point.chi := by linarith [hchi.1]
  have hcombine :
      (Real.log point.k + lrLowKIdealQChi point.chi) *
          (1 + point.chi) =
        Real.log point.k +
          point.chi * (Real.log point.k + Real.log point.chi) := by
    unfold lrLowKIdealQChi
    field_simp [hden.ne']
    ring
  unfold lrDA7FiniteA
  rw [le_div_iff₀ hden, hcombine]
  nlinarith [houterLog, hweighted]

lemma lrOneToFour_finiteS_nonpos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (_hdeep : LRDeterminantDeepRegion point)
    (_hkFour : point.k ≤ 4) :
    lrDA7FiniteS point ≤ 0 := by
  have hA := lrOneToFour_log_k_add_qChi_le_finiteA hinterior
  unfold lrDA7FiniteS lrDA7FiniteP lrDA7FiniteG
  linarith [hinterior.1.1]

end CourtadeKumar
