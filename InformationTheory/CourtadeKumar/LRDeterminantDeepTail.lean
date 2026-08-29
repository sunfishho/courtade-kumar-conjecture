import InformationTheory.CourtadeKumar.LRDeterminantThickReserve
import InformationTheory.CourtadeKumar.LRDeterminantRegionAssembly
import InformationTheory.CourtadeKumar.LRUniformTailOmega

/-!
# Deep analytic tail for the audited determinant

This module proves the analytic half of the audited deep-region split.  On
`s ≤ 2⁻¹⁴` and `k ≥ 128`, entropy-remainder estimates give a positive
normalized singular determinant, hence an admitted determinant certificate.
The complementary strip `s ≤ k ≤ 128` is intentionally left to the audited
bounded-`k` certificate.
-/

open Set

namespace CourtadeKumar

/-- The half-slope base is uniformly below `60/7` once `v ≥ 1/3`. -/
theorem lrLowHalfSlopeBase_lt_sixty_sevenths_of_one_third_le
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvThird : 1 / 3 ≤ v) :
    lrLowHalfSlopeBase v < 60 / 7 := by
  let p := lrFlowM v / 2
  let z := p / (2 - p)
  have hvPlus : 0 < 1 + v := by linarith [hv.1]
  have hpFormula : p = v / (2 * (1 + v)) := by
    unfold p lrFlowM
    field_simp [hvPlus.ne']
  have hpPos : 0 < p := by
    rw [hpFormula]
    exact div_pos hv.1 (mul_pos (by norm_num) hvPlus)
  have hpLower : 1 / 8 ≤ p := by
    rw [hpFormula, le_div_iff₀ (mul_pos (by norm_num) hvPlus)]
    nlinarith
  have hpUpper : p ≤ 1 / 4 := by
    rw [hpFormula, div_le_iff₀ (mul_pos (by norm_num) hvPlus)]
    nlinarith [hv.2]
  have hpOne : 0 < 1 - p := by linarith
  have hpTwo : 0 < 2 - p := by linarith
  have hzPos : 0 < z := div_pos hpPos hpTwo
  have hzLt : z < 1 := by
    unfold z
    rw [div_lt_one hpTwo]
    linarith [hpUpper]
  have hzMem : z ∈ Ico (0 : ℝ) 1 := ⟨hzPos.le, hzLt⟩
  have hzFull : z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hzPos], hzLt.le⟩
  have hzRatio : (1 + z) / (1 - z) = 1 / (1 - p) := by
    have hzOne : 1 - z ≠ 0 := by linarith [hzLt]
    rw [div_eq_iff hzOne]
    unfold z
    field_simp [hpTwo.ne', hpOne.ne']
    ring
  have hlogInv : Real.log (1 / (1 - p)) = -Real.log (1 - p) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hpOne.ne',
      Real.log_one]
    ring
  have hart := artanh_le_cubicPade_unit hzMem
  rw [Real.artanh_eq_half_log hzFull, hzRatio, hlogInv] at hart
  have hnegLog : -Real.log (1 - p) ≤
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2))) := by
    nlinarith
  have hbase : 0 < 1 - z ^ 2 := by nlinarith [hzPos, hzLt]
  have hbaseFormula :
      1 - z ^ 2 = 4 * (1 - p) / (2 - p) ^ 2 := by
    unfold z
    field_simp [hpTwo.ne']
    ring
  have hPadeFormula :
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2))) =
        p * (12 * (1 - p) + p ^ 2) /
          (6 * (1 - p) * (2 - p)) := by
    rw [hbaseFormula]
    unfold z
    field_simp [hpTwo.ne', hpOne.ne']
    ring
  have hquad : 0 < 360 * p ^ 2 - 1042 * p + 2695 / 4 := by
    nlinarith [hpUpper, sq_nonneg p]
  have hfactor : 0 ≤ (p - 1 / 8) *
      (360 * p ^ 2 - 1042 * p + 2695 / 4) :=
    mul_nonneg (sub_nonneg.mpr hpLower) hquad.le
  have hpoly :
      7 * (12 * (1 - p) + p ^ 2) <
        360 * p * (1 - p) * (2 - p) := by
    nlinarith [hfactor]
  have hden : 0 < 6 * (1 - p) * (2 - p) :=
    mul_pos (mul_pos (by norm_num) hpOne) hpTwo
  have hPadeBound :
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2))) <
        60 / 7 * p ^ 2 := by
    rw [hPadeFormula, div_lt_iff₀ hden]
    have hscaled := mul_pos hpPos (sub_pos.mpr hpoly)
    nlinarith
  unfold lrLowHalfSlopeBase
  change -Real.log (1 - p) / p ^ 2 < 60 / 7
  rw [div_lt_iff₀ (sq_pos_of_pos hpPos)]
  exact hnegLog.trans_lt hPadeBound

/-- Deep-tail upper bound `H_d < log (1/s) + 9`. -/
theorem lrDeterminantHd_lt_log_add_nine
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hsDeep : point.s ≤ 1 / 16384) :
    lrDeterminantHd point < Real.log (1 / point.s) + 9 := by
  let s := point.s
  let R := lrCertificateR point
  let v := lrCertificateV point
  let L := Real.log (1 / s)
  have hs : s ∈ Ioc (0 : ℝ) (1 / 16384) := ⟨hinterior.1.1, hsDeep⟩
  have hR : R ∈ Ioo (0 : ℝ) 1 := by
    unfold R lrCertificateR
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvThird := lrCertificateV_one_third_le_of_physical
    hinterior hphysical
  have hhalf : lrCertificateHalfSlope point = lrFlowHalfSlope R v := by
    simpa [R, v] using lrCertificateHalfSlope_eq_flow
      hinterior.1 hinterior.2.1
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hscale : 1 - R = s := by
    dsimp [R, lrCertificateR, s]
    ring
  have hHd : lrDeterminantHd point =
      lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1 := by
    unfold lrDeterminantHd
    change lrCertificateHalfSlope point / s = _
    rw [hhalf, lrFlowHalfSlope_eq_normalized hR.2.ne, hscale]
    field_simp [hs.1.ne']
  have hEnergy : 4 * lrNormalizedEnergy R 1 =
      4 * lrCertificateQ s / s - 4 * Real.log 2 := by
    unfold lrNormalizedEnergy
    rw [topPhi_one, lrCertificateQ_eq]
    have hREq : R = 1 - s := by
      dsimp [R, lrCertificateR, s]
    rw [hREq]
    simp only [mul_one]
    rw [show 1 - (1 - s) = s by ring]
    change 4 * (((1 - s) * Real.log 2 -
        topPhi (Real.sqrt (1 - s))) / s) =
      4 * (Real.log 2 - topPhi (Real.sqrt (1 - s))) / s -
        4 * Real.log 2
    field_simp [hs.1.ne']
    ring
  have hsSixteenth : s ∈ Ioc (0 : ℝ) (1 / 16 : ℝ) :=
    ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hQ := lrCertificateQ_upper_sixteenth hsSixteenth
  have hlogSplit : Real.log (4 / s) = L + 2 * Real.log 2 := by
    dsimp [L]
    rw [show 4 / s = 4 * (1 / s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hs.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  rw [hlogSplit] at hQ
  have hbase := lrLowHalfSlopeBase_lt_sixty_sevenths_of_one_third_le
    hv hvThird
  change lrLowHalfSlopeBase v < 60 / 7 at hbase
  have hlogEndpoint :
      Real.log (4 / (1 / 16384 : ℝ)) = 16 * Real.log 2 := by
    rw [show (4 / (1 / 16384 : ℝ)) = 2 ^ 16 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (4 / (1 / 16384 : ℝ)) := by
    rw [hlogEndpoint]
    nlinarith [Real.log_two_gt_d9]
  have hmulLog := mul_log_four_div_le_endpoint hs.1
    (by norm_num : (0 : ℝ) < 1 / 16384) hs.2 hendpointOne
  rw [hlogEndpoint, hlogSplit] at hmulLog
  have hsmall :
      4 * s / 9 * (L + 2 * Real.log 2) < 1 / 3000 := by
    have hlogUpper : Real.log 2 < 7 / 10 := by
      nlinarith [Real.log_two_lt_d9]
    nlinarith
  rw [hHd, hEnergy]
  have hQscaled : 4 * lrCertificateQ s / s ≤
      (1 + 4 * s / 9) * (L + 2 * Real.log 2) + 1 := by
    rw [div_le_iff₀ hs.1]
    nlinarith
  dsimp [L, s] at hQscaled hbase hsmall ⊢
  nlinarith [Real.log_two_gt_d9]

/-- The radial entropy kernel obeys the endpoint bound `W ≤ s/4`. -/
theorem lrCertificateW_le_quarter
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateW point ≤ point.s / 4 := by
  change lrCertificateOmega point.s 0 ≤ point.s / 4
  exact (lrCertificateOmega_zero_mem hinterior.1).2

/-- Both cancellation-kernel terms are nonnegative in the open chart. -/
theorem lrCertificatePW_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrCertificatePW point := by
  have hs := hinterior.1
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hy0 : lrCertificateY0 point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_pos hinterior.2.2.1 he.1
    · calc
        point.chi * lrCertificateE point <
            1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 he.1
        _ < 1 := by simpa using he.2
  have homegaY0 := lrCertificateOmega_lower hs hy0
  have homegaE := lrCertificateOmega_lower hs he
  have hY0Nonnegative :
      0 ≤ lrCertificateOmega point.s (lrCertificateY0 point) := by
    apply le_trans _ homegaY0
    exact div_nonneg
      (mul_nonneg (sq_nonneg point.s)
        (sq_nonneg (1 - lrCertificateY0 point)))
      (mul_nonneg (by norm_num) (add_nonneg hy0.1.le hs.1.le))
  have hENonnegative :
      0 ≤ lrCertificateOmega point.s (lrCertificateE point) := by
    apply le_trans _ homegaE
    exact div_nonneg
      (mul_nonneg (sq_nonneg point.s)
        (sq_nonneg (1 - lrCertificateE point)))
      (mul_nonneg (by norm_num) (add_nonneg he.1.le hs.1.le))
  unfold lrCertificatePW lrCertificatePWValue
  exact add_nonneg hY0Nonnegative (div_nonneg hENonnegative hv.1.le)

/-- Sparse-identity loss bound `Ψ - G ≥ -3s/4` on the physical chart. -/
theorem lrDeterminantPsi_sub_GShape_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point) :
    -(3 / 4) * point.s ≤
      lrDeterminantPsi point - lrCertificateGShape point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvThird := lrCertificateV_one_third_le_of_physical
    hinterior hphysical
  have hden : 0 < 1 + lrCertificateV point := by linarith [hv.1]
  have hcoeff : 4 / (1 + lrCertificateV point) ≤ 3 := by
    rw [div_le_iff₀ hden]
    linarith
  have hWPos := (lrCertificateOmega_zero_mem hinterior.1).1.le
  have hWUpper := lrCertificateW_le_quarter hinterior
  have hloss : 4 * lrCertificateW point /
      (1 + lrCertificateV point) ≤ 3 * point.s / 4 := by
    calc
      4 * lrCertificateW point / (1 + lrCertificateV point) =
          (4 / (1 + lrCertificateV point)) *
            lrCertificateW point := by ring
      _ ≤ 3 * lrCertificateW point :=
        mul_le_mul_of_nonneg_right hcoeff hWPos
      _ ≤ 3 * (point.s / 4) :=
        mul_le_mul_of_nonneg_left hWUpper (by norm_num)
      _ = 3 * point.s / 4 := by ring
  have hPW := lrCertificatePW_nonnegative hinterior
  unfold lrDeterminantPsi
  linarith

/-- Deep-tail lower bound `1 / (4 (log (1/s) + 9)) < c₀`. -/
theorem lrDeterminantC0_deep_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hsDeep : point.s ≤ 1 / 16384) :
    1 / (4 * (Real.log (1 / point.s) + 9)) <
      lrDeterminantC0 point := by
  let L := Real.log (1 / point.s)
  let R := lrCertificateR point
  let Wn := 4 * lrCertificateW point / point.s
  let Hd := lrDeterminantHd point
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
    ⟨hinterior.1.1, hsDeep⟩
  have hL := lrSmallSBridge_log_lower hs
  have hLPos : 0 < L := by
    dsimp [L] at hL ⊢
    nlinarith [Real.log_two_gt_d9]
  have hPPos : 0 < L + 9 := by linarith
  have hRLower : 999 / 1000 < R := by
    dsimp [R, lrCertificateR]
    nlinarith [hsDeep]
  have hRPos : 0 < R := (by norm_num : (0 : ℝ) < 999 / 1000).trans hRLower
  have hWnLower : 999 / 1000 < Wn := by
    simpa [Wn] using lrCertificateW_normalized_gt_999_div_1000 hs
  have hWnPos : 0 < Wn :=
    (by norm_num : (0 : ℝ) < 999 / 1000).trans hWnLower
  have hprodLower : 3 / 4 < R * Wn := by
    have hdiff := mul_pos (sub_pos.mpr hRLower) (sub_pos.mpr hWnLower)
    nlinarith
  have hHdPos : 0 < Hd := by
    simpa [Hd] using lrDeterminantHd_pos hinterior
  have hHdUpper : Hd < L + 9 := by
    simpa [Hd, L] using
      lrDeterminantHd_lt_log_add_nine hinterior hphysical hsDeep
  have hc0 : lrDeterminantC0 point = R * Wn / (3 * Hd) := by
    unfold lrDeterminantC0
    dsimp [R, Wn, Hd]
    field_simp [hinterior.1.1.ne']
  rw [hc0]
  rw [div_lt_div_iff₀
    (mul_pos (by norm_num) hPPos)
    (mul_pos (by norm_num) hHdPos)]
  have hleft : 3 * Hd < 3 * (L + 9) :=
    mul_lt_mul_of_pos_left hHdUpper (by norm_num)
  have hright : 3 * (L + 9) < R * Wn * (4 * (L + 9)) := by
    have hscaled := mul_lt_mul_of_pos_right hprodLower
      (mul_pos (by norm_num : (0 : ℝ) < 4) hPPos)
    nlinarith
  nlinarith

/-- Cross-multiplied form of the audited `55/21` logarithmic ratio. -/
theorem lrDeepTail_log_cross
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 16384)) :
    21 * (Real.log (1 / s) + 9) ≤
      55 * (Real.log (1 / s) - 5 * Real.log 2 + 1) := by
  have hL := lrSmallSBridge_log_lower hs
  have hlam : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  nlinarith

/-- Entropy reserve `G ≥ Q(128s) ≥ 32s(L - 5 log 2 + 1)`. -/
theorem lrCertificateGShape_deepTail_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hk : 128 ≤ point.k) :
    32 * point.s *
        (Real.log (1 / point.s) - 5 * Real.log 2 + 1) ≤
      lrCertificateGShape point := by
  have hs := hinterior.1
  have he := hinterior.2.1
  have h128E : 128 * point.s ≤ lrCertificateE point := by
    unfold lrCertificateE
    nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hk)]
  have h128Mem : 128 * point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos (by norm_num) hs.1, h128E.trans_lt he.2⟩
  have hQMono := lrCertificateQ_strictMonoOn.monotoneOn
    h128Mem he h128E
  have hQ0 := lrLowerFaceQ0_le_Q
    (show 128 * point.s ∈ Ioc (0 : ℝ) 1 from
      ⟨h128Mem.1, h128Mem.2.le⟩)
  have hQG := lrCertificateQ_E_le_GShape hinterior
  have hlogScale :
      Real.log (4 / (128 * point.s)) =
        Real.log (1 / point.s) - 5 * Real.log 2 := by
    rw [show 4 / (128 * point.s) = (1 / point.s) / 32 by
      field_simp [hs.1.ne']
      norm_num,
      Real.log_div (one_div_ne_zero hs.1.ne')
        (by norm_num : (32 : ℝ) ≠ 0),
      show Real.log 32 = 5 * Real.log 2 by
        rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
        norm_num]
  have hQ0Eq : lrLowerFaceQ0 (128 * point.s) =
      32 * point.s *
        (Real.log (1 / point.s) - 5 * Real.log 2 + 1) := by
    unfold lrLowerFaceQ0
    rw [hlogScale]
    ring
  rw [← hQ0Eq]
  exact hQ0.trans (hQMono.trans hQG)

/-- The exact rational endgame of the deep-tail determinant estimate. -/
lemma lrDeepTail_scalar_lower
    {s P D G : ℝ}
    (hs : 0 ≤ s) (hP : 0 < P) (hG : 0 < G)
    (hcross : 21 * P ≤ 55 * D)
    (hGLower : 32 * s * D ≤ G) :
    201 / (4480 * P) ≤
      -(3 * s) / (4 * G) + 17 / (160 * P) := by
  have hnumerator : 3360 * s * P ≤ 275 * G := by
    calc
      3360 * s * P = (160 * s) * (21 * P) := by ring
      _ ≤ (160 * s) * (55 * D) :=
        mul_le_mul_of_nonneg_left hcross
          (mul_nonneg (by norm_num) hs)
      _ = 8800 * s * D := by ring
      _ = 275 * (32 * s * D) := by ring
      _ ≤ 275 * G :=
        mul_le_mul_of_nonneg_left hGLower (by norm_num)
  have hquot : 0 ≤
      (275 * G - 3360 * s * P) / (4480 * P * G) :=
    div_nonneg (sub_nonneg.mpr hnumerator)
      (mul_nonneg (mul_nonneg (by norm_num) hP.le) hG.le)
  have hid :
      (-(3 * s) / (4 * G) + 17 / (160 * P)) -
          201 / (4480 * P) =
        (275 * G - 3360 * s * P) / (4480 * P * G) := by
    field_simp [hP.ne', hG.ne']
    ring
  rw [← hid] at hquot
  linarith

/-- The normalized singular determinant is strictly positive in the deep tail. -/
theorem lrDeterminantNormalized_deepTail_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsDeep : point.s ≤ 1 / 16384)
    (hk : 128 ≤ point.k) :
    0 < lrDeterminantNormalized
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrDeterminantPsi point / lrCertificateGShape point)
      (4 * lrDeterminantDelta point * lrCertificateW point /
        lrCertificateGShape point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point / lrCertificateGShape point) := by
  let L := Real.log (1 / point.s)
  let P := L + 9
  let D := L - 5 * Real.log 2 + 1
  let G := lrCertificateGShape point
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
    ⟨hinterior.1.1, hsDeep⟩
  have hL := lrSmallSBridge_log_lower hs
  have hPPos : 0 < P := by
    dsimp [P, L]
    nlinarith [Real.log_two_gt_d9]
  have hGPos : 0 < G := by
    simpa [G] using lrCertificateGShape_pos hinterior
  have hcross : 21 * P ≤ 55 * D := by
    simpa [P, D, L] using lrDeepTail_log_cross hs
  have hGLower : 32 * point.s * D ≤ G := by
    simpa [D, L, G] using lrCertificateGShape_deepTail_lower hinterior hk
  have hscalarLower := lrDeepTail_scalar_lower
    hinterior.1.1.le hPPos hGPos hcross hGLower
  have hcertificatePos : 0 < 201 / (4480 * P) :=
    div_pos (by norm_num) (mul_pos (by norm_num) hPPos)
  have hscalar :
      0 < -(3 * point.s) / (4 * G) + 17 / (160 * P) :=
    hcertificatePos.trans_le hscalarLower
  have hPsiSub := lrDeterminantPsi_sub_GShape_lower hinterior hrelevant.1
  have hPsiNorm : -(3 * point.s) / (4 * G) ≤
      lrDeterminantPsi point / G - 1 := by
    have hdiv := div_le_div_of_nonneg_right hPsiSub hGPos.le
    calc
      -(3 * point.s) / (4 * G) =
          (-(3 / 4) * point.s) / G := by ring
      _ ≤ (lrDeterminantPsi point - lrCertificateGShape point) / G := hdiv
      _ = lrDeterminantPsi point / G - 1 := by
        rw [sub_div, div_self]
        exact (lrCertificateGShape_pos hinterior).ne'
  have hC0 := lrDeterminantC0_deep_lower hinterior hrelevant.1 hsDeep
  have hX : 17 / 20 ≤ lrCertificateX point := by
    have hphysical := hrelevant.1
    unfold lrCertificateX lrCertificateE
    unfold LRHighShapePhysical at hphysical
    linarith [hphysical.2.1]
  have hTheta := lrDeterminantTheta_ge_half_of_k_ge_sixteen
    hinterior hrelevant (by linarith : 16 ≤ point.k)
  have hC0Pos : 0 < lrDeterminantC0 point :=
    (div_pos (by norm_num)
      (mul_pos (by norm_num) hPPos)).trans hC0
  have hCterm : 17 / (160 * P) <
      lrDeterminantC0 point * lrCertificateX point *
        (lrDeterminantT point / G) := by
    calc
      17 / (160 * P) =
          (1 / (4 * P)) * (17 / 20) * (1 / 2) := by
        field_simp [hPPos.ne']
        ring
      _ < lrDeterminantC0 point * (17 / 20) * (1 / 2) :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hC0 (by norm_num)) (by norm_num)
      _ ≤ lrDeterminantC0 point * lrCertificateX point * (1 / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX hC0Pos.le) (by norm_num)
      _ ≤ lrDeterminantC0 point * lrCertificateX point *
          (lrDeterminantT point / G) :=
        mul_le_mul_of_nonneg_left hTheta
          (mul_nonneg hC0Pos.le (by linarith [hX]))
  have hRd : 0 ≤ 4 * lrDeterminantDelta point *
      lrCertificateW point / G :=
    div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (lrDeterminantDelta_nonnegative hinterior))
        (lrCertificateW_pos hinterior).le)
      hGPos.le
  have hCoeff := lrCertificateDeterminantCoefficient_nonnegative hinterior
  have hDterm : 0 ≤
      lrDeterminantD1 point / lrCertificateBFlow point *
        (lrDeterminantPsi point / G -
          lrDeterminantC0 point * (lrDeterminantT point / G)) := by
    exact mul_nonneg
      (div_nonneg (lrDeterminantD1_nonnegative hinterior)
        (lrCertificateBFlow_pos hinterior).le)
      (by simpa [G] using hCoeff)
  unfold lrDeterminantNormalized
  dsimp [G] at hPsiNorm hCterm hRd hDterm ⊢
  linarith

/-- The cleared singular target is strictly positive in the deep tail. -/
theorem lrDeterminantClearedSingular_deepTail_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsDeep : point.s ≤ 1 / 16384)
    (hk : 128 ≤ point.k) :
    0 < lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point) := by
  have hB := lrCertificateBFlow_pos hinterior
  have hG := lrCertificateGShape_pos hinterior
  rw [lrDeterminantClearedSingular_eq_normalized hB.ne' hG.ne']
  exact mul_pos (mul_pos hB hG)
    (lrDeterminantNormalized_deepTail_pos hinterior hrelevant hsDeep hk)

/-- Pointwise admitted determinant certificate for the analytic deep tail. -/
theorem lrDeterminantAdmittedTarget_deepTail
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsDeep : point.s ≤ 1 / 16384)
    (hk : 128 ≤ point.k) :
    LRDeterminantAdmittedTarget point := by
  right
  exact (lrDeterminantClearedSingular_deepTail_pos
    hinterior hrelevant hsDeep hk).le

/-- The analytic subregion of the manuscript's deep split. -/
def LRDeterminantDeepTailRegion (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 16384 ∧ 128 ≤ point.k

/-- The deep analytic tail supplies a determinant-region certificate. -/
theorem lrDeterminantDeepTailRegion_certificate :
    LRDeterminantRegionCertificateTheorem LRDeterminantDeepTailRegion := by
  intro point hinterior hrelevant hregion
  exact lrDeterminantAdmittedTarget_deepTail
    hinterior hrelevant hregion.1 hregion.2

end CourtadeKumar
