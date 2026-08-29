import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreAssembly

/-!
# Finite-stage restoration on the restricted deep band `1 <= k <= 4`

This module isolates the first (finite-`s`, frozen-channel) stage of
the restricted bounded-deep restoration.  It uses the generic algebraic
collector already proved for DA7, but replaces the old `k <= 1` analytic
inputs by arguments valid on the physical deep band.

The endpoint calculation deliberately uses the audited low-band constants

* `s0 = 2^-14`,
* the conservative `e0 = 2^-10`, and
* `Lplus = 49/5`.

No executable proof shortcut or generated certificate is used.
-/

open Set

namespace CourtadeKumar
namespace LRRestrictedOneToFourFiniteStage

/-! ## Exact bridge between the two ideal-core APIs -/

theorem idealH_one_add_eq (t : ℝ) :
    lrLowKIdealH (1 + t) = lrDeterminantIdealH t := by
  simp [lrLowKIdealH, lrDeterminantIdealH]

theorem idealC_eq : lrLowKIdealC = lrDeterminantIdealC := by
  rfl

theorem idealA_eq (k chi : ℝ) :
    lrLowKIdealA k chi = lrDeterminantIdealA k chi := by
  rfl

theorem idealAH_eq (k chi : ℝ) :
    lrLowKIdealAH k chi = lrDeterminantIdealAH k chi := by
  simp only [lrLowKIdealAH, lrDeterminantIdealAH, idealH_one_add_eq]

theorem idealQChi_eq (chi : ℝ) :
    lrLowKIdealQChi chi = lrSmallSBridgeQChi chi := by
  rfl

theorem idealD_eq (k : ℝ) :
    lrLowKIdealD k = lrDeterminantIdealD0 k := by
  rfl

theorem idealBOffset_eq (k : ℝ) :
    lrLowKIdealBOffset k = lrDeterminantIdealBConst k := by
  rfl

theorem idealB_eq (L k : ℝ) :
    lrDeterminantIdealB0 L k = L / 2 + lrLowKIdealBOffset k := by
  unfold lrDeterminantIdealB0 lrLowKIdealBOffset
  ring

theorem idealP_eq (L k chi : ℝ) :
    lrDeterminantIdealP L k chi = L + lrLowKIdealP k chi := by
  unfold lrDeterminantIdealP lrLowKIdealP
  rw [idealA_eq]
  ring

theorem idealP_sub_G_eq (L k chi : ℝ) :
    lrDeterminantIdealP L k chi - lrDeterminantIdealG L k chi =
      lrLowKIdealS k chi := by
  unfold lrDeterminantIdealP lrDeterminantIdealG lrLowKIdealS
  rw [idealA_eq, idealQChi_eq]
  ring

theorem idealT_eq (L k chi : ℝ) :
    lrDeterminantIdealT L k chi = L + lrLowKIdealT k chi := by
  unfold lrDeterminantIdealT lrLowKIdealT
  rw [idealAH_eq]
  ring

theorem idealCore_eq (L k chi : ℝ) :
    lrLowKIdealCore L k chi = lrDeterminantIdealCore L k chi := by
  unfold lrLowKIdealCore lrDeterminantIdealCore
  dsimp only
  rw [idealD_eq, idealP_sub_G_eq, idealP_eq, idealB_eq,
    idealBOffset_eq, idealT_eq, idealC_eq]

/-! ## Restricted endpoint constants -/

noncomputable def restrictedS0 : ℝ := 1 / 2 ^ 14

noncomputable def restrictedE0 : ℝ := 1 / 2 ^ 10

noncomputable def restrictedLPlus : ℝ := 49 / 5

noncomputable def restrictedFiniteEndpoint : ℝ :=
  (restrictedS0 * restrictedLPlus + restrictedS0 ^ 2) / 2 +
    (restrictedS0 * restrictedLPlus + (12 / 5) * restrictedS0) / 2 +
    (restrictedS0 * restrictedLPlus / 2 + (7 / 10) * restrictedS0) +
    (restrictedE0 * restrictedLPlus + 4 * restrictedE0) / 2 +
    restrictedE0 * restrictedS0 / 2 +
    (restrictedS0 * restrictedLPlus / 6 + (8 / 15) * restrictedS0) +
    (restrictedE0 * restrictedLPlus / 6 + (3 / 5) * restrictedE0)

theorem restrictedFiniteEndpoint_eq :
    restrictedFiniteEndpoint = lrBoundedDeepLowFiniteEndpoint := by
  norm_num [restrictedFiniteEndpoint, restrictedS0, restrictedE0,
    restrictedLPlus, lrBoundedDeepLowFiniteEndpoint]

/-! ## Exact global signs for the two `S` coordinates -/

/-- The ideal angular coordinate is nonpositive for every positive `k`.
The proof keeps the exact two logarithmic comparisons visible. -/
theorem idealS_nonpos_of_k_pos
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    lrLowKIdealS k chi ≤ 0 := by
  rcases hchi.1.eq_or_lt with rfl | hchiPos
  · have houter : Real.log k ≤ Real.log (1 + k) :=
      Real.log_le_log hk (by linarith)
    simpa [lrLowKIdealS, lrLowKIdealQChi, lrLowKIdealA,
      sub_nonpos] using houter
  · have hkchi : 0 < k * chi := mul_pos hk hchiPos
    have hinner :
        Real.log (k * chi) ≤ Real.log (1 + k * chi) :=
      Real.log_le_log hkchi (by linarith)
    have houter : Real.log k ≤ Real.log (1 + k) :=
      Real.log_le_log hk (by linarith)
    have hlogMul :
        Real.log (k * chi) = Real.log k + Real.log chi := by
      rw [Real.log_mul hk.ne' hchiPos.ne']
    rw [hlogMul] at hinner
    have hweighted := mul_le_mul_of_nonneg_left hinner hchiPos.le
    have hden : 0 < 1 + chi := by linarith
    have hformula :
        lrLowKIdealS k chi =
          (chi * (Real.log k + Real.log chi) + Real.log k -
            (chi * Real.log (1 + k * chi) + Real.log (1 + k))) /
            (1 + chi) := by
      unfold lrLowKIdealS lrLowKIdealQChi lrLowKIdealA
      field_simp [hden.ne']
      ring
    rw [hformula]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

/-- The finite frozen angular coordinate is nonpositive throughout the
physical chart.  The two key inequalities are exactly
`k <= 1 + (1-s)k` and
`k chi <= 1 + (1-s)k chi`, both consequences of `s k < 1`. -/
theorem finiteS_nonpos_of_physical
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7FiniteS point ≤ 0 := by
  have hs := hinterior.1.1
  have hk := lrBoundedDeep_k_pos hinterior
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
  have hkchi : 0 < point.k * point.chi := mul_pos hk hchi.1
  have houterLog :
      Real.log point.k ≤
        Real.log (1 + (1 - point.s) * point.k) :=
    Real.log_le_log hk houterOrder
  have hinnerLog :
      Real.log (point.k * point.chi) ≤
        Real.log (1 + (1 - point.s) * point.k * point.chi) :=
    Real.log_le_log hkchi hinnerOrder
  have hlogMul :
      Real.log (point.k * point.chi) =
        Real.log point.k + Real.log point.chi := by
    rw [Real.log_mul hk.ne' hchi.1.ne']
  rw [hlogMul] at hinnerLog
  have hweighted := mul_le_mul_of_nonneg_left hinnerLog hchi.1.le
  have hden : 0 < 1 + point.chi :=
    add_pos_of_pos_of_nonneg (by norm_num) hchi.1.le
  have hformula :
      lrDA7FiniteS point =
        (point.chi * (Real.log point.k + Real.log point.chi) +
            Real.log point.k -
          (point.chi *
              Real.log (1 + (1 - point.s) * point.k * point.chi) +
            Real.log (1 + (1 - point.s) * point.k)) -
          point.s * (1 + point.chi)) /
          (1 + point.chi) := by
    unfold lrDA7FiniteS lrDA7FiniteP lrDA7FiniteG lrDA7FiniteA
      lrLowKIdealQChi
    field_simp [hden.ne']
    ring
  rw [hformula]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hden.le

/-! ## Common consequences of the restricted deep hypotheses -/

theorem log_scale_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    14 * Real.log 2 ≤ Real.log (1 / point.s) := by
  exact lrSmallSBridge_log_lower ⟨hinterior.1.1, hdeep.1⟩

theorem log_scale_ge_forty_nine_tenths
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    (49 / 10 : ℝ) ≤ Real.log (1 / point.s) := by
  have hL := log_scale_lower hinterior hdeep
  nlinarith [Real.log_two_gt_d9]

theorem log_scale_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    0 < Real.log (1 / point.s) := by
  have hL := log_scale_lower hinterior hdeep
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem e_le_restrictedE0
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrCertificateE point ≤ restrictedE0 := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hs0 : 0 ≤ point.s := hinterior.1.1.le
  have hfirst := mul_le_mul_of_nonneg_right hdeep.1 hk.le
  have hsecond := mul_le_mul_of_nonneg_left hkFour
    (show (0 : ℝ) ≤ 1 / 16384 by norm_num)
  unfold lrCertificateE
  dsimp [restrictedE0]
  calc
    point.s * point.k ≤ (1 / 16384 : ℝ) * point.k := hfirst
    _ ≤ (1 / 16384 : ℝ) * 4 := hsecond
    _ ≤ 1 / 2 ^ 10 := by norm_num

theorem s_mul_log_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    point.s * Real.log (1 / point.s) ≤
      restrictedS0 * restrictedLPlus := by
  have hsMem : point.s ∈ Ioc (0 : ℝ) restrictedS0 := by
    refine ⟨hinterior.1.1, ?_⟩
    convert hdeep.1 using 1 <;> norm_num [restrictedS0]
  have hendpointLog :
      Real.log (1 / restrictedS0) = 14 * Real.log 2 := by
    dsimp [restrictedS0]
    rw [show (1 / (1 / 2 ^ 14 : ℝ)) = 2 ^ 14 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (1 / restrictedS0) := by
    rw [hendpointLog]
    nlinarith [Real.log_two_gt_d9]
  have hmul := lrDA7_mul_log_inv_le_endpoint hsMem.1
    (show 0 < restrictedS0 by norm_num [restrictedS0]) hsMem.2
    hendpointOne
  have hlogUpper :
      Real.log (1 / restrictedS0) ≤ restrictedLPlus := by
    rw [hendpointLog]
    dsimp [restrictedLPlus]
    nlinarith [Real.log_two_lt_d9]
  have hscaled := mul_le_mul_of_nonneg_left hlogUpper
    (show 0 ≤ restrictedS0 by norm_num [restrictedS0])
  exact hmul.trans hscaled

theorem e_mul_log_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrCertificateE point * Real.log (1 / point.s) ≤
      restrictedE0 * restrictedLPlus := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hL := log_scale_pos hinterior hdeep
  have hsL := s_mul_log_upper hinterior hdeep
  have hfirst := mul_le_mul_of_nonneg_left hsL hk.le
  have hendpoint0 : 0 ≤ restrictedS0 * restrictedLPlus := by
    norm_num [restrictedS0, restrictedLPlus]
  have hsecond := mul_le_mul_of_nonneg_right hkFour hendpoint0
  have hid :
      lrCertificateE point * Real.log (1 / point.s) =
        point.k * (point.s * Real.log (1 / point.s)) := by
    unfold lrCertificateE
    ring
  rw [hid]
  calc
    point.k * (point.s * Real.log (1 / point.s)) ≤
        point.k * (restrictedS0 * restrictedLPlus) := hfirst
    _ ≤ 4 * (restrictedS0 * restrictedLPlus) := hsecond
    _ ≤ restrictedE0 * restrictedLPlus := by
      norm_num [restrictedS0, restrictedE0, restrictedLPlus]

/-! ## Generalized coordinate bounds -/

/-- The exact determinant-coordinate comparison only needs the physical
condition `s*k < 1`; it does not need `k <= 1`. -/
theorem determinantD1_finite_bounds_of_physical
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrLowKIdealD point.k - point.s / 2 ≤ lrDeterminantD1 point ∧
      lrDeterminantD1 point ≤ lrLowKIdealD point.k := by
  have hs := hinterior.1.1
  have hk := lrBoundedDeep_k_pos hinterior
  have heLt : point.s * point.k < 1 := by
    simpa [lrCertificateE] using hinterior.2.1.2
  have hskInv : point.s ≤ 1 / point.k := by
    rw [le_div_iff₀ hk]
    exact heLt.le
  have hY : 1 ≤ 1 + 1 / point.k - point.s := by linarith
  have hmodel := lrDA7DModel_finite_loss hY hs.le
  have hshift :
      1 + 1 / point.k - point.s + point.s = 1 + 1 / point.k := by
    ring
  rw [hshift] at hmodel
  rw [lrLowKIdealD_eq_DModel hk,
    lrDeterminantD1_eq_DModel hs hk]
  exact ⟨hmodel.2, hmodel.1⟩

theorem log_one_add_k_le_four
    {k : ℝ} (hk : 0 < k) (hkFour : k ≤ 4) :
    Real.log (1 + k) ≤ 4 := by
  have harg : 0 < 1 + k := by linarith
  have hlogOrder : Real.log (1 + k) ≤ Real.log 5 :=
    Real.log_le_log harg (by linarith)
  have hlogFive : Real.log (5 : ℝ) ≤ 4 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5) using 1 <;>
      norm_num
  exact hlogOrder.trans hlogFive

theorem idealA_nonnegative
    {k chi : ℝ} (hk : 0 < k) (hchi : chi ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrLowKIdealA k chi := by
  have hinner : 1 ≤ 1 + k * chi := by
    exact le_add_of_nonneg_right (mul_nonneg hk.le hchi.1)
  have houter : 1 ≤ 1 + k := by linarith
  have hden : 0 ≤ 1 + chi :=
    add_nonneg (by norm_num) hchi.1
  unfold lrLowKIdealA
  exact div_nonneg
    (add_nonneg (mul_nonneg hchi.1 (Real.log_nonneg hinner))
      (Real.log_nonneg houter)) hden

theorem idealB_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 < lrDA7IdealB point := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hL := log_scale_ge_forty_nine_tenths hinterior hdeep
  have hlog := log_one_add_k_le_four hk hkFour
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrDA7IdealB lrLowKIdealBOffset
  nlinarith

theorem idealB_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7IdealB point ≤
      Real.log (1 / point.s) / 2 + 7 / 10 := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hlogK : 0 ≤ Real.log (1 + point.k) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealB lrLowKIdealBOffset
  linarith

theorem idealPFull_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 < lrDA7IdealPFull point := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hA := lrLowKIdealA_le_log_one_add hk hchi
  have hlog := log_one_add_k_le_four hk hkFour
  have hL := log_scale_ge_forty_nine_tenths hinterior hdeep
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrDA7IdealPFull lrLowKIdealP
  linarith

theorem idealPFull_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7IdealPFull point ≤ Real.log (1 / point.s) + 12 / 5 := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hA := idealA_nonnegative hk hchi
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealPFull lrLowKIdealP
  linarith

theorem idealTFull_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    0 < lrDA7IdealTFull point := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hAH := lrLowKIdealAH_le_one_add_log hk hchi
  have hlog := log_one_add_k_le_four hk hkFour
  have hL := log_scale_ge_forty_nine_tenths hinterior hdeep
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold lrDA7IdealTFull lrLowKIdealT
  linarith

theorem idealTFull_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDA7IdealTFull point ≤ Real.log (1 / point.s) + 7 / 5 := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hAH := lrLowKIdealAH_ge_one hk hchi
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold lrDA7IdealTFull lrLowKIdealT
  linarith

theorem idealCStar_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    0 ≤ lrDA7IdealCStar point := by
  have hL := log_scale_lower hinterior hdeep
  have hden : 0 < Real.log (1 / point.s) + lrLowKIdealC := by
    have hbase := lrLowKIdealL0_add_C_pos
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold lrLowKIdealL0 at hbase
    linarith [hL]
  unfold lrDA7IdealCStar
  positivity

theorem idealCStar_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point) :
    lrDA7IdealCStar point ≤
      1 / (3 * Real.log (1 / point.s)) := by
  have hL := log_scale_pos hinterior hdeep
  have hdenL : 0 < 3 * Real.log (1 / point.s) :=
    mul_pos (by norm_num) hL
  have hdenOrder :
      3 * Real.log (1 / point.s) ≤
        3 * (Real.log (1 / point.s) + lrLowKIdealC) := by
    nlinarith [lrDA7IdealC_nonnegative]
  unfold lrDA7IdealCStar
  exact one_div_le_one_div_of_le hdenL hdenOrder

theorem idealS_abs_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k)
    (hkFour : point.k ≤ 4) :
    -lrLowKIdealS point.k point.chi ≤
      Real.log (1 / point.s) + 4 := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hlogK : 0 ≤ Real.log point.k := Real.log_nonneg hkOne
  have hA := lrLowKIdealA_le_log_one_add hk hchi
  have hlog := log_one_add_k_le_four hk hkFour
  have hq := lrSmallSBridgeQChi_lower hchi
  have hqEq : lrLowKIdealQChi point.chi =
      lrSmallSBridgeQChi point.chi := rfl
  have hL := log_scale_ge_forty_nine_tenths hinterior hdeep
  unfold lrLowKIdealS
  rw [hqEq]
  linarith

/-! ## The generalized finite-core comparison -/

theorem finite_frozen_core_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k)
    (hkFour : point.k ≤ 4) :
    lrLowKIdealCore (Real.log (1 / point.s)) point.k point.chi -
        lrDA7FiniteSymbolicLoss point.s (lrCertificateE point)
          (lrLowKIdealD point.k) (lrDA7IdealB point)
          (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
          (lrDA7IdealTFull point) (lrDA7IdealCStar point) ≤
      lrDA7FiniteFrozenCore point := by
  have hk := lrBoundedDeep_k_pos hinterior
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hD := determinantD1_finite_bounds_of_physical hinterior
  have hBInterval := lrDA7FiniteB_ideal_interval hinterior
  have hB0 := (idealB_pos hinterior hdeep hkFour).le
  have hB : 0 ≤ lrDA7FiniteB point := hB0.trans hBInterval.1
  have hx := lrDA7_x_loss_bounds hinterior
  have hscalar := lrDA7_finite_scalar_core_lower
    (s := point.s) (e := lrCertificateE point)
    (D0 := lrLowKIdealD point.k) (D := lrDeterminantD1 point)
    (B0 := lrDA7IdealB point) (B := lrDA7FiniteB point)
    (p := lrDA7IdealPFull point) (ps := lrDA7FiniteP point)
    (S := lrLowKIdealS point.k point.chi) (Ss := lrDA7FiniteS point)
    (t := lrDA7IdealTFull point) (ts := lrDA7FiniteT point)
    (c := lrDA7IdealCStar point) (x := lrCertificateX point)
    hinterior.1.1.le hinterior.1.2.le hinterior.2.1.1.le
    (lrDeterminantD1_nonnegative hinterior)
    hD.1 hD.2 hB0 hB hBInterval.1 hBInterval.2
    (idealPFull_pos hinterior hdeep hkFour).le
    (lrDA7FiniteP_lower hinterior)
    (idealS_nonpos_of_k_pos hk hchi)
    (lrDA7FiniteS_lower hinterior)
    (idealTFull_pos hinterior hdeep hkFour).le
    (lrDA7FiniteT_lower hinterior)
    (idealCStar_nonnegative hinterior hdeep)
    hx.1 hx.2 (lrDA7FiniteGap_pos hinterior hrelevant).le
  rw [lrLowKIdealCore_eq_scalarCore,
    lrDA7FiniteFrozenCore_eq_scalarCore]
  exact hscalar

/-! ## Seven-term endpoint envelope -/

theorem finite_cubic_upper
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkFour : point.k ≤ 4) :
    lrDA7IdealCStar point *
        (point.s * (lrDA7IdealB point - lrLowKIdealD point.k) +
          lrCertificateE point *
            (lrDA7IdealB point + lrCertificateE point / 2)) *
        lrDA7IdealTFull point ≤
      point.s * (Real.log (1 / point.s) / 6 + 8 / 15) +
        lrCertificateE point *
          (Real.log (1 / point.s) / 6 + 3 / 5) := by
  let L := Real.log (1 / point.s)
  let e := lrCertificateE point
  let D0 := lrLowKIdealD point.k
  let B0 := lrDA7IdealB point
  let c := lrDA7IdealCStar point
  let t := lrDA7IdealTFull point
  let bracket := point.s * (B0 - D0) + e * (B0 + e / 2)
  have hs0 : 0 ≤ point.s := hinterior.1.1.le
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact hinterior.2.1.1.le
  have heUpper : e ≤ restrictedE0 := by
    simpa [e] using e_le_restrictedE0 hinterior hdeep hkFour
  have hL : (49 / 10 : ℝ) ≤ L := by
    simpa [L] using log_scale_ge_forty_nine_tenths hinterior hdeep
  have hLpos : 0 < L := by linarith
  have hinv0 : 0 ≤ 1 / (3 * L) := by
    exact (one_div_pos.mpr (mul_pos (by norm_num) hLpos)).le
  have hD0 : 0 ≤ D0 := by
    dsimp [D0]
    exact (lrLowKIdealD_pos (lrBoundedDeep_k_pos hinterior)).le
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact (idealB_pos hinterior hdeep hkFour).le
  have hB0Upper : B0 ≤ L / 2 + 7 / 10 := by
    simpa [B0, L] using idealB_upper hinterior
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact idealCStar_nonnegative hinterior hdeep
  have hcUpper : c ≤ 1 / (3 * L) := by
    simpa [c, L] using idealCStar_upper hinterior hdeep
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact (idealTFull_pos hinterior hdeep hkFour).le
  have htUpper : t ≤ L + 7 / 5 := by
    simpa [t, L] using idealTFull_upper hinterior
  have hbracketUpper :
      bracket ≤
        point.s * (L / 2 + 7 / 10) +
          e * (L / 2 + 7 / 10 + e / 2) := by
    have hfirst : point.s * (B0 - D0) ≤ point.s * B0 := by
      nlinarith [mul_nonneg hs0 hD0]
    have hfirstUpper := mul_le_mul_of_nonneg_left hB0Upper hs0
    have hsumNonneg : 0 ≤ B0 + e / 2 := by positivity
    have hsecondUpper :
        e * (B0 + e / 2) ≤
          e * (L / 2 + 7 / 10 + e / 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) he0
    dsimp [bracket]
    linarith
  have hsCoefficient :
      (1 / (3 * L)) * (L / 2 + 7 / 10) * (L + 7 / 5) ≤
        L / 6 + 8 / 15 := by
    have hid :
        (1 / (3 * L)) * (L / 2 + 7 / 10) * (L + 7 / 5) =
          ((L / 2 + 7 / 10) * (L + 7 / 5)) / (3 * L) := by
      ring
    rw [hid]
    rw [div_le_iff₀ (mul_pos (by norm_num) hLpos)]
    nlinarith
  have heCoefficient :
      (1 / (3 * L)) * (L / 2 + 7 / 10 + e / 2) *
          (L + 7 / 5) ≤
        L / 6 + 3 / 5 := by
    have hcoef : 0 ≤ (2 / 5 : ℝ) - e / 2 := by
      dsimp [restrictedE0] at heUpper
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hL hcoef
    have hgap :
        0 ≤ ((2 / 5 : ℝ) - e / 2) * L -
          (49 / 50 + 7 * e / 10) := by
      dsimp [restrictedE0] at heUpper
      nlinarith
    have hid :
        (1 / (3 * L)) * (L / 2 + 7 / 10 + e / 2) *
            (L + 7 / 5) =
          ((L / 2 + 7 / 10 + e / 2) * (L + 7 / 5)) /
            (3 * L) := by
      ring
    rw [hid]
    rw [div_le_iff₀ (mul_pos (by norm_num) hLpos)]
    nlinarith
  by_cases hbracket : 0 ≤ bracket
  · have hupperBracketNonneg :
        0 ≤ point.s * (L / 2 + 7 / 10) +
          e * (L / 2 + 7 / 10 + e / 2) :=
      hbracket.trans hbracketUpper
    have hstepC :
        c * bracket * t ≤
          (1 / (3 * L)) * bracket * t := by
      have hfactor : 0 ≤ bracket * t := mul_nonneg hbracket ht0
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right hcUpper hfactor)
    have hstepBracket :
        (1 / (3 * L)) * bracket * t ≤
          (1 / (3 * L)) *
            (point.s * (L / 2 + 7 / 10) +
              e * (L / 2 + 7 / 10 + e / 2)) * t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbracketUpper hinv0) ht0
    have hstepT :
        (1 / (3 * L)) *
            (point.s * (L / 2 + 7 / 10) +
              e * (L / 2 + 7 / 10 + e / 2)) * t ≤
          (1 / (3 * L)) *
            (point.s * (L / 2 + 7 / 10) +
              e * (L / 2 + 7 / 10 + e / 2)) * (L + 7 / 5) := by
      exact mul_le_mul_of_nonneg_left htUpper
        (mul_nonneg hinv0 hupperBracketNonneg)
    have hsScaled := mul_le_mul_of_nonneg_left hsCoefficient hs0
    have heScaled := mul_le_mul_of_nonneg_left heCoefficient he0
    have hsplit :
        (1 / (3 * L)) *
            (point.s * (L / 2 + 7 / 10) +
              e * (L / 2 + 7 / 10 + e / 2)) * (L + 7 / 5) =
          point.s *
              ((1 / (3 * L)) * (L / 2 + 7 / 10) * (L + 7 / 5)) +
            e * ((1 / (3 * L)) *
              (L / 2 + 7 / 10 + e / 2) * (L + 7 / 5)) := by
      ring
    change c * bracket * t ≤
      point.s * (L / 6 + 8 / 15) + e * (L / 6 + 3 / 5)
    calc
      c * bracket * t ≤ (1 / (3 * L)) * bracket * t := hstepC
      _ ≤ (1 / (3 * L)) *
          (point.s * (L / 2 + 7 / 10) +
            e * (L / 2 + 7 / 10 + e / 2)) * t := hstepBracket
      _ ≤ (1 / (3 * L)) *
          (point.s * (L / 2 + 7 / 10) +
            e * (L / 2 + 7 / 10 + e / 2)) * (L + 7 / 5) := hstepT
      _ = point.s *
            ((1 / (3 * L)) * (L / 2 + 7 / 10) * (L + 7 / 5)) +
          e * ((1 / (3 * L)) *
            (L / 2 + 7 / 10 + e / 2) * (L + 7 / 5)) := hsplit
      _ ≤ point.s * (L / 6 + 8 / 15) +
          e * (L / 6 + 3 / 5) := add_le_add hsScaled heScaled
  · have hbracketNonpos : bracket ≤ 0 := le_of_not_ge hbracket
    have hleft : c * bracket * t ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hc0 hbracketNonpos) ht0
    have hright :
        0 ≤ point.s * (L / 6 + 8 / 15) +
          e * (L / 6 + 3 / 5) := by
      have hsFactor : 0 ≤ L / 6 + 8 / 15 := by linarith
      have heFactor : 0 ≤ L / 6 + 3 / 5 := by linarith
      exact add_nonneg (mul_nonneg hs0 hsFactor)
        (mul_nonneg he0 heFactor)
    change c * bracket * t ≤
      point.s * (L / 6 + 8 / 15) + e * (L / 6 + 3 / 5)
    exact hleft.trans hright

theorem symbolic_loss_le_restricted_endpoint
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k)
    (hkFour : point.k ≤ 4) :
    lrDA7FiniteSymbolicLoss point.s (lrCertificateE point)
        (lrLowKIdealD point.k) (lrDA7IdealB point)
        (lrDA7IdealPFull point) (lrLowKIdealS point.k point.chi)
        (lrDA7IdealTFull point) (lrDA7IdealCStar point) ≤
      restrictedFiniteEndpoint := by
  let L := Real.log (1 / point.s)
  let e := lrCertificateE point
  have hsUpper : point.s ≤ restrictedS0 := by
    convert hdeep.1 using 1 <;> norm_num [restrictedS0]
  have heUpper : e ≤ restrictedE0 := by
    simpa [e] using e_le_restrictedE0 hinterior hdeep hkFour
  have hs0 : 0 ≤ point.s := hinterior.1.1.le
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact hinterior.2.1.1.le
  have hL0 : 0 ≤ L := (log_scale_pos hinterior hdeep).le
  have hsL : point.s * L ≤ restrictedS0 * restrictedLPlus := by
    simpa [L] using s_mul_log_upper hinterior hdeep
  have heL : e * L ≤ restrictedE0 * restrictedLPlus := by
    simpa [e, L] using e_mul_log_upper hinterior hdeep hkFour
  have hsSq : point.s ^ 2 ≤ restrictedS0 ^ 2 := by
    exact pow_le_pow_left₀ hs0 hsUpper 2
  have hes : e * point.s ≤ restrictedE0 * restrictedS0 := by
    exact mul_le_mul heUpper hsUpper hs0
      (show 0 ≤ restrictedE0 by norm_num [restrictedE0])
  have hD := lrDA7IdealD_upper hinterior.1.1
    (hdeep.1.trans (by norm_num [lrDA7S0])) hdeep.2
  have hDterm :
      point.s * lrLowKIdealD point.k ≤
        (restrictedS0 * restrictedLPlus + restrictedS0 ^ 2) / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hD hs0
    nlinarith
  have hP := idealPFull_upper hinterior
  have hPterm :
      point.s / 2 * lrDA7IdealPFull point ≤
        (restrictedS0 * restrictedLPlus + (12 / 5) * restrictedS0) / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hP
      (show 0 ≤ point.s / 2 from div_nonneg hs0 (by norm_num))
    have hlinear := mul_le_mul_of_nonneg_left hsUpper
      (show (0 : ℝ) ≤ 12 / 5 by norm_num)
    nlinarith
  have hB := idealB_upper hinterior
  have hBterm :
      point.s * lrDA7IdealB point ≤
        restrictedS0 * restrictedLPlus / 2 +
          (7 / 10) * restrictedS0 := by
    have hscaled := mul_le_mul_of_nonneg_left hB hs0
    have hlinear := mul_le_mul_of_nonneg_left hsUpper
      (show (0 : ℝ) ≤ 7 / 10 by norm_num)
    nlinarith
  have hSnonpos := idealS_nonpos_of_k_pos
    (lrBoundedDeep_k_pos hinterior)
    (show point.chi ∈ Icc (0 : ℝ) 1 from
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
  have hS := idealS_abs_upper hinterior hdeep hkOne hkFour
  have hSterm :
      e / 2 * (-lrLowKIdealS point.k point.chi) ≤
        (restrictedE0 * restrictedLPlus + 4 * restrictedE0) / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hS
      (show 0 ≤ e / 2 from div_nonneg he0 (by norm_num))
    have hlinear := mul_le_mul_of_nonneg_left heUpper
      (show (0 : ℝ) ≤ 4 by norm_num)
    nlinarith
  have hesTerm : e * point.s / 2 ≤
      restrictedE0 * restrictedS0 / 2 := by nlinarith
  have hc := finite_cubic_upper hinterior hdeep hkFour
  have hcEndpoint :
      lrDA7IdealCStar point *
          (point.s * (lrDA7IdealB point - lrLowKIdealD point.k) +
            e * (lrDA7IdealB point + e / 2)) *
          lrDA7IdealTFull point ≤
        (restrictedS0 * restrictedLPlus / 6 +
            (8 / 15) * restrictedS0) +
          (restrictedE0 * restrictedLPlus / 6 +
            (3 / 5) * restrictedE0) := by
    have hsPart :
        point.s * (L / 6 + 8 / 15) ≤
          restrictedS0 * restrictedLPlus / 6 +
            (8 / 15) * restrictedS0 := by
      have hlinear := mul_le_mul_of_nonneg_left hsUpper
        (show (0 : ℝ) ≤ 8 / 15 by norm_num)
      nlinarith
    have hePart :
        e * (L / 6 + 3 / 5) ≤
          restrictedE0 * restrictedLPlus / 6 +
            (3 / 5) * restrictedE0 := by
      have hlinear := mul_le_mul_of_nonneg_left heUpper
        (show (0 : ℝ) ≤ 3 / 5 by norm_num)
      nlinarith
    simpa [e, L] using hc.trans (add_le_add hsPart hePart)
  unfold lrDA7FiniteSymbolicLoss restrictedFiniteEndpoint
  dsimp [e, L] at hDterm hPterm hBterm hSterm hesTerm hcEndpoint ⊢
  linarith

/-! ## Exact restricted `finiteLow` output -/

/-- The finite-stage inequality required by a specialized
`LRDeterminantDeepOneToFourRestorationTheorem`.

This is deliberately stated with the exact restricted deep hypotheses,
rather than the larger `k <= 16` compact-region interface. -/
theorem finiteLow_oneToFour
    (point : CertificatePoint)
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hdeep : LRDeterminantDeepRegion point)
    (hkOne : 1 ≤ point.k)
    (hkFour : point.k ≤ 4) :
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point ≤
      lrBoundedDeepLowFiniteEndpoint := by
  have hcore := finite_frozen_core_lower
    hinterior hrelevant hdeep hkOne hkFour
  have henvelope := symbolic_loss_le_restricted_endpoint
    hinterior hdeep hkOne hkFour
  rw [idealCore_eq] at hcore
  rw [← restrictedFiniteEndpoint_eq]
  linarith

/-- Adapter with the exact compact-region prefix used by the existing
bounded-deep analytic-input record, but restricted to `1 <= k <= 4`. -/
theorem finiteLow_oneToFour_compact
    (point : CertificatePoint)
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hregion : LRDeterminantBoundedDeepCompactRegion point)
    (hkOne : 1 ≤ point.k)
    (hkFour : point.k ≤ 4) :
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrDA7FiniteFrozenCore point ≤
      lrBoundedDeepLowFiniteEndpoint := by
  exact finiteLow_oneToFour point hinterior hrelevant
    ⟨hregion.1, hregion.2.1⟩ hkOne hkFour

end LRRestrictedOneToFourFiniteStage
end CourtadeKumar
