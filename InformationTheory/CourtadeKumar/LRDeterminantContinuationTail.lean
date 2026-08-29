import InformationTheory.CourtadeKumar.LRDeterminantDeepTail

/-!
# Analytic continuation tail for the audited determinant

This module proves the continuation-tail row of the audited determinant
ledger.  On `s ≤ 2⁻⁷` and `k ≥ 32`, the exact sparse cancellation and
two complementary entropy estimates give a positive normalized singular
determinant, hence an admitted determinant certificate.
-/

open Set

namespace CourtadeKumar

/-- Exact `H_d` decomposition used throughout the continuation tail. -/
lemma lrDeterminantHd_eq_continuationTail
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDeterminantHd point =
      lrLowHalfSlopeBase (lrCertificateV point) +
        4 * lrCertificateQ point.s / point.s - 4 * Real.log 2 := by
  let R := lrCertificateR point
  let v := lrCertificateV point
  have hR : R ∈ Ioo (0 : ℝ) 1 := by
    dsimp [R, lrCertificateR]
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hhalf :
      lrCertificateHalfSlope point = lrFlowHalfSlope R v := by
    simpa [R, v] using lrCertificateHalfSlope_eq_flow
      hinterior.1 hinterior.2.1
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hscale : 1 - R = point.s := by
    dsimp [R, lrCertificateR]
    ring
  have hHd : lrDeterminantHd point =
      lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1 := by
    unfold lrDeterminantHd
    rw [hhalf, lrFlowHalfSlope_eq_normalized hR.2.ne, hscale]
    field_simp [hinterior.1.1.ne']
  have hEnergy : 4 * lrNormalizedEnergy R 1 =
      4 * lrCertificateQ point.s / point.s - 4 * Real.log 2 := by
    unfold lrNormalizedEnergy
    rw [topPhi_one, lrCertificateQ_eq]
    have hREq : R = 1 - point.s := by
      dsimp [R, lrCertificateR]
    rw [hREq]
    simp only [mul_one]
    rw [show 1 - (1 - point.s) = point.s by ring]
    field_simp [hinterior.1.1.ne']
    ring
  rw [hHd, hEnergy]
  dsimp [v]
  ring

/-- A rational lower bound for the half-slope base on the physical range.
It is the exact strength needed for the manuscript constant `146/35`. -/
lemma lrLowHalfSlopeBase_ge_thirty_two_sevenths
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    32 / 7 ≤ lrLowHalfSlopeBase v := by
  let p := lrFlowM v / 2
  let u := p / (1 - p)
  have hvPlus : 0 < 1 + v := by linarith [hv.1]
  have hpFormula : p = v / (2 * (1 + v)) := by
    unfold p lrFlowM
    field_simp [hvPlus.ne']
  have hpPos : 0 < p := by
    rw [hpFormula]
    exact div_pos hv.1 (mul_pos (by norm_num) hvPlus)
  have hpUpper : p ≤ 1 / 4 := by
    rw [hpFormula, div_le_iff₀ (mul_pos (by norm_num) hvPlus)]
    nlinarith [hv.2]
  have hpOne : 0 < 1 - p := by linarith
  have huNonnegative : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg hpPos.le hpOne.le
  have hlog := lr_log_one_add_lower huNonnegative
  have huArg : 1 + u = 1 / (1 - p) := by
    dsimp [u]
    field_simp [hpOne.ne']
    ring
  have hlogInv : Real.log (1 / (1 - p)) = -Real.log (1 - p) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hpOne.ne',
      Real.log_one]
    ring
  have hPade : 2 * p / (2 - p) ≤ -Real.log (1 - p) := by
    rw [huArg, hlogInv] at hlog
    have hpTwo : 0 < 2 - p := by linarith
    have hrewrite : 2 * u / (2 + u) = 2 * p / (2 - p) := by
      dsimp [u]
      field_simp [hpOne.ne', hpTwo.ne']
      ring
    rwa [hrewrite] at hlog
  have hpTwo : 0 < 2 - p := by linarith
  have hfactor : 0 ≤ (1 / 4 - p) * (7 / 4 - p) :=
    mul_nonneg (sub_nonneg.mpr hpUpper) (by nlinarith [hpUpper])
  have hpoly : p * (2 - p) ≤ 7 / 16 := by
    nlinarith [hfactor]
  have htarget : (32 / 7) * p ^ 2 ≤ 2 * p / (2 - p) := by
    rw [le_div_iff₀ hpTwo]
    have hscaleNonnegative : 0 ≤ (32 / 7 : ℝ) * p :=
      mul_nonneg (by norm_num) hpPos.le
    have hscaled := mul_le_mul_of_nonneg_left hpoly hscaleNonnegative
    nlinarith
  unfold lrLowHalfSlopeBase
  change 32 / 7 ≤ -Real.log (1 - p) / p ^ 2
  rw [le_div_iff₀ (sq_pos_of_pos hpPos)]
  exact htarget.trans hPade

/-- Continuation-tail lower bound `H_d > L + 146/35`. -/
lemma lrDeterminantHd_continuationTail_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    Real.log (1 / point.s) + 146 / 35 < lrDeterminantHd point := by
  let L := Real.log (1 / point.s)
  have hs := hinterior.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hbase := lrLowHalfSlopeBase_ge_thirty_two_sevenths hv
  have hQ0 := lrLowerFaceQ0_le_Q
    (show point.s ∈ Ioc (0 : ℝ) 1 from ⟨hs.1, hs.2.le⟩)
  have hlogSplit : Real.log (4 / point.s) = L + 2 * Real.log 2 := by
    dsimp [L]
    rw [show 4 / point.s = 4 * (1 / point.s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hs.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  unfold lrLowerFaceQ0 at hQ0
  rw [hlogSplit] at hQ0
  have hQscaled : L + 2 * Real.log 2 + 1 ≤
      4 * lrCertificateQ point.s / point.s := by
    rw [le_div_iff₀ hs.1]
    nlinarith
  rw [lrDeterminantHd_eq_continuationTail hinterior]
  dsimp [L] at hQscaled ⊢
  nlinarith [Real.log_two_lt_d9]

/-- The `Q(s)/H_d` payment in (DA6) is strictly below `9s/32`. -/
lemma lrDeterminantQ_div_Hd_continuationTail_lt
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hsSmall : point.s ≤ 1 / 128) :
    lrCertificateQ point.s / lrDeterminantHd point < 9 * point.s / 32 := by
  let L := Real.log (1 / point.s)
  let P := L + 146 / 35
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hs16 : point.s ∈ Ioc (0 : ℝ) (1 / 16 : ℝ) :=
    ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hL : 7 * Real.log 2 ≤ L := by
    have harg : (128 : ℝ) ≤ 1 / point.s := by
      rw [le_div_iff₀ hs.1]
      nlinarith [hs.2]
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 128) harg
    have hpow : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    simpa [L, hpow] using hlog
  have hPPos : 0 < P := by
    dsimp [P]
    nlinarith [Real.log_two_gt_d9]
  have hHdLower : P < lrDeterminantHd point := by
    simpa [P, L] using lrDeterminantHd_continuationTail_lower hinterior
  have hlogSplit : Real.log (4 / point.s) = L + 2 * Real.log 2 := by
    dsimp [L]
    rw [show 4 / point.s = 4 * (1 / point.s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hs.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  have hlogEndpoint :
      Real.log (4 / (1 / 128 : ℝ)) = 9 * Real.log 2 := by
    rw [show (4 / (1 / 128 : ℝ)) = 2 ^ 9 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (4 / (1 / 128 : ℝ)) := by
    rw [hlogEndpoint]
    nlinarith [Real.log_two_gt_d9]
  have hmulLog := mul_log_four_div_le_endpoint hs.1
    (by norm_num : (0 : ℝ) < 1 / 128) hs.2 hendpointOne
  rw [hlogEndpoint, hlogSplit] at hmulLog
  have hQ := lrCertificateQ_upper_sixteenth hs16
  rw [hlogSplit] at hQ
  have hQscaled : 4 * lrCertificateQ point.s / point.s ≤
      (1 + 4 * point.s / 9) * (L + 2 * Real.log 2) + 1 := by
    rw [div_le_iff₀ hs.1]
    nlinarith
  have hcore :
      (1 + 4 * point.s / 9) * (L + 2 * Real.log 2) + 1 <
        (9 / 8) * P := by
    dsimp [P]
    nlinarith [Real.log_two_lt_d9]
  have hQlt : lrCertificateQ point.s < (9 * point.s / 32) * P := by
    have h := hQscaled.trans_lt hcore
    rw [div_le_iff₀ hs.1] at hQscaled
    have hscaled := mul_lt_mul_of_pos_right h hs.1
    nlinarith
  have hfactor : 0 < 9 * point.s / 32 :=
    div_pos (mul_pos (by norm_num) hs.1) (by norm_num)
  have hQltHd : lrCertificateQ point.s <
      (9 * point.s / 32) * lrDeterminantHd point :=
    hQlt.trans (mul_lt_mul_of_pos_left hHdLower hfactor)
  rw [div_lt_iff₀ (lrDeterminantHd_pos hinterior)]
  nlinarith

/-- Exact sparse cancellation used in the continuation tail. -/
lemma lrDeterminantSparseCancellation_continuationTail
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDeterminantPsi point - lrCertificateGShape point +
        4 * lrDeterminantDelta point * lrCertificateW point =
      lrCertificatePW point -
        4 * lrCertificateV point * lrCertificateX point *
          lrCertificateW point / (1 + lrCertificateV point) := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hden : 1 + lrCertificateV point ≠ 0 := by linarith [hv.1]
  unfold lrDeterminantPsi lrDeterminantDelta
  field_simp [hden]
  ring

/-- The sparse cancellation loses at most `x*s/2`. -/
lemma lrDeterminantSparse_continuationTail_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    -(lrCertificateX point * point.s / 2) ≤
      lrDeterminantPsi point - lrCertificateGShape point +
        4 * lrDeterminantDelta point * lrCertificateW point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hX : lrCertificateX point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateX
    have hprodPos := mul_pos hinterior.2.2.1 hinterior.2.1.1
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    constructor <;> linarith
  have hW0 := (lrCertificateW_pos hinterior).le
  have hW := lrCertificateW_le_quarter hinterior
  have hden : 0 < 1 + lrCertificateV point := by linarith [hv.1]
  have hvCoeff : lrCertificateV point / (1 + lrCertificateV point) ≤
      1 / 2 := by
    rw [div_le_iff₀ hden]
    linarith [hv.2]
  have hkernel :
      4 * lrCertificateV point * lrCertificateW point /
          (1 + lrCertificateV point) ≤ point.s / 2 := by
    have hcoeff := mul_le_mul_of_nonneg_left hvCoeff
      (by norm_num : (0 : ℝ) ≤ 4)
    have hmul := mul_le_mul_of_nonneg_right hcoeff hW0
    calc
      4 * lrCertificateV point * lrCertificateW point /
          (1 + lrCertificateV point) =
        (4 * (lrCertificateV point /
          (1 + lrCertificateV point))) * lrCertificateW point := by ring
      _ ≤ (4 * (1 / 2 : ℝ)) * lrCertificateW point := hmul
      _ ≤ point.s / 2 := by nlinarith [hW]
  have hscaled := mul_le_mul_of_nonneg_left hkernel hX.1.le
  rw [lrDeterminantSparseCancellation_continuationTail hinterior]
  have hPW := lrCertificatePW_nonnegative hinterior
  calc
    -(lrCertificateX point * point.s / 2) =
        -(lrCertificateX point * (point.s / 2)) := by ring
    _ ≤ -(lrCertificateX point *
        (4 * lrCertificateV point * lrCertificateW point /
          (1 + lrCertificateV point))) := neg_le_neg hscaled
    _ = -(4 * lrCertificateV point * lrCertificateX point *
        lrCertificateW point / (1 + lrCertificateV point)) := by ring
    _ ≤ lrCertificatePW point -
        4 * lrCertificateV point * lrCertificateX point *
          lrCertificateW point / (1 + lrCertificateV point) := by linarith

/-- Kernel-safe form of (DA6), before inserting either entropy branch. -/
lemma lrDeterminantNormalized_continuationTail_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point) :
    lrCertificateX point *
        (lrDeterminantC0 point -
          (point.s / 2 +
              lrCertificateQ point.s / lrDeterminantHd point) /
            lrCertificateGShape point) ≤
      lrDeterminantNormalized
        (lrCertificateBFlow point) (lrDeterminantD1 point)
        (lrDeterminantPsi point / lrCertificateGShape point)
        (4 * lrDeterminantDelta point * lrCertificateW point /
          lrCertificateGShape point)
        (lrDeterminantC0 point) (lrCertificateX point)
        (lrDeterminantT point / lrCertificateGShape point) := by
  let B := lrCertificateBFlow point
  let D1 := lrDeterminantD1 point
  let G := lrCertificateGShape point
  let Psi := lrDeterminantPsi point
  let delta := lrDeterminantDelta point
  let W := lrCertificateW point
  let c0 := lrDeterminantC0 point
  let x := lrCertificateX point
  let T := lrDeterminantT point
  let Q := lrCertificateQ point.s
  let Hd := lrDeterminantHd point
  have hs := hinterior.1.1
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hB : 0 < B := by simpa [B] using lrCertificateBFlow_pos hinterior
  have hG : 0 < G := by simpa [G] using lrCertificateGShape_pos hinterior
  have hHd : 0 < Hd := by simpa [Hd] using lrDeterminantHd_pos hinterior
  have hW0 : 0 ≤ W := by simpa [W] using (lrCertificateW_pos hinterior).le
  have hWUpper : W ≤ point.s / 4 := by
    simpa [W] using lrCertificateW_le_quarter hinterior
  have hQ : 0 ≤ Q := by
    simpa [Q] using lrCertificateQ_nonneg
      ⟨hinterior.1.1.le, hinterior.1.2.le⟩
  have hX : x ∈ Ioo (0 : ℝ) 1 := by
    dsimp [x, lrCertificateX]
    have hprodPos := mul_pos hinterior.2.2.1 hinterior.2.1.1
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    constructor <;> linarith
  have hc0 : 0 ≤ c0 := by
    simpa [c0] using lrDeterminantC0_nonnegative hs hHd
      hR.le hW0
  have hD1 : 0 ≤ D1 := by
    simpa [D1] using lrDeterminantD1_nonnegative hinterior
  have hCoeff : c0 * T ≤ Psi := by
    have h := lrCertificateDeterminantCoefficient_nonnegative hinterior
    change 0 ≤ Psi / G - c0 * (T / G) at h
    rw [sub_nonneg] at h
    rw [show c0 * (T / G) = (c0 * T) / G by ring] at h
    exact (div_le_div_iff_of_pos_right hG).mp h
  have hcancel : -(x * point.s / 2) ≤
      Psi - G + 4 * delta * W := by
    simpa [x, Psi, G, delta, W] using lrDeterminantSparse_continuationTail_lower hinterior
  have hfirst : B * (-(x * point.s / 2) + c0 * x * T) ≤
      lrDeterminantClearedSingular B D1 G Psi delta W c0 x T := by
    have hcancelScaled := mul_le_mul_of_nonneg_left hcancel hB.le
    have hcoeffTerm : 0 ≤ D1 * (Psi - c0 * T) :=
      mul_nonneg hD1 (sub_nonneg.mpr hCoeff)
    unfold lrDeterminantClearedSingular
    nlinarith
  have hT : G - 3 * Q / lrCertificateR point ≤ T := by
    simpa [G, Q, T] using lrDeterminantT_thick_lower hinterior hrelevant
  have hTscaled :
      B * (-(x * point.s / 2) +
          c0 * x * (G - 3 * Q / lrCertificateR point)) ≤
        B * (-(x * point.s / 2) + c0 * x * T) := by
    have h := mul_le_mul_of_nonneg_left hT (mul_nonneg hc0 hX.1.le)
    have h' := mul_le_mul_of_nonneg_left h hB.le
    nlinarith
  have hWnorm : 4 * W / point.s ≤ 1 := by
    rw [div_le_one hs]
    nlinarith [hWUpper]
  have hQHd : 0 ≤ Q / Hd := div_nonneg hQ hHd.le
  have hcostEq :
      c0 * (3 * Q / lrCertificateR point) =
        (4 * W / point.s) * (Q / Hd) := by
    dsimp [c0, W, Q, Hd]
    unfold lrDeterminantC0
    field_simp [hs.ne', hR.ne', hHd.ne']
  have hcost : c0 * (3 * Q / lrCertificateR point) ≤ Q / Hd := by
    rw [hcostEq]
    calc
      (4 * W / point.s) * (Q / Hd) ≤ 1 * (Q / Hd) :=
        mul_le_mul_of_nonneg_right hWnorm hQHd
      _ = Q / Hd := one_mul _
  have hcostScaled :
      B * x * (c0 * (3 * Q / lrCertificateR point)) ≤
        B * x * (Q / Hd) :=
    mul_le_mul_of_nonneg_left hcost (mul_nonneg hB.le hX.1.le)
  apply (mul_le_mul_iff_of_pos_left (mul_pos hB hG)).mp
  rw [← lrDeterminantClearedSingular_eq_normalized hB.ne' hG.ne']
  calc
    B * G *
        (x * (c0 - (point.s / 2 + Q / Hd) / G)) =
      B * x * (-(point.s / 2) + c0 * G - Q / Hd) := by
        field_simp [hG.ne']
        ring
    _ ≤ B * (-(x * point.s / 2) +
          c0 * x * (G - 3 * Q / lrCertificateR point)) := by
      nlinarith
    _ ≤ B * (-(x * point.s / 2) + c0 * x * T) := hTscaled
    _ ≤ lrDeterminantClearedSingular B D1 G Psi delta W c0 x T := hfirst

/-- The endpoint estimate for `s log (1/s)` used in both DA6 branches. -/
lemma lrDeterminantContinuationTail_mul_log_four_upper
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ)) :
    s * (Real.log (1 / s) + 2 * Real.log 2) ≤
      (1 / 128 : ℝ) * (9 * Real.log 2) := by
  have hlogEndpoint :
      Real.log (4 / (1 / 128 : ℝ)) = 9 * Real.log 2 := by
    rw [show (4 / (1 / 128 : ℝ)) = 2 ^ 9 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (4 / (1 / 128 : ℝ)) := by
    rw [hlogEndpoint]
    nlinarith [Real.log_two_gt_d9]
  have hmul := mul_log_four_div_le_endpoint hs.1
    (by norm_num : (0 : ℝ) < 1 / 128) hs.2 hendpointOne
  have hlogSplit :
      Real.log (4 / s) = Real.log (1 / s) + 2 * Real.log 2 := by
    rw [show 4 / s = 4 * (1 / s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hs.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  rwa [hlogEndpoint, hlogSplit] at hmul

/-- In the large-entropy branch the radial logarithmic factor is small. -/
lemma lrDeterminantContinuationTail_s_mul_log_add_lt
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ)) :
    s * (Real.log (1 / s) + 33 / 4) < 263 / 2560 := by
  have hmul := lrDeterminantContinuationTail_mul_log_four_upper hs
  have hcoeff : 0 ≤ 33 / 4 - 2 * Real.log 2 := by
    nlinarith [Real.log_two_lt_d9]
  have hlinear := mul_le_mul_of_nonneg_right hs.2 hcoeff
  nlinarith [Real.log_two_lt_d9]

/-- Continuation-tail upper bound for `H_d` in the branch `e >= 1/2`. -/
lemma lrDeterminantHd_continuationTail_upper_largeE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hsSmall : point.s ≤ 1 / 128) :
    lrDeterminantHd point < Real.log (1 / point.s) + 33 / 4 := by
  let L := Real.log (1 / point.s)
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hs16 : point.s ∈ Ioc (0 : ℝ) (1 / 16 : ℝ) :=
    ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvThird := lrCertificateV_one_third_le_of_physical
    hinterior hphysical
  have hbase :=
    lrLowHalfSlopeBase_lt_sixty_sevenths_of_one_third_le hv hvThird
  have hmul := lrDeterminantContinuationTail_mul_log_four_upper hs
  have hlogSplit : Real.log (4 / point.s) = L + 2 * Real.log 2 := by
    dsimp [L]
    rw [show 4 / point.s = 4 * (1 / point.s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hs.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  have hQ := lrCertificateQ_upper_sixteenth hs16
  rw [hlogSplit] at hQ
  have hQscaled : 4 * lrCertificateQ point.s / point.s ≤
      (1 + 4 * point.s / 9) * (L + 2 * Real.log 2) + 1 := by
    rw [div_le_iff₀ hs.1]
    nlinarith
  rw [lrDeterminantHd_eq_continuationTail hinterior]
  dsimp [L] at hQscaled hmul ⊢
  nlinarith [Real.log_two_gt_d9]

/-- On `e >= 1/2`, the shape entropy has the audited numerical floor. -/
lemma lrCertificateGShape_continuationTail_gt_largeE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (heHalf : 1 / 2 ≤ lrCertificateE point) :
    3079 / 8000 < lrCertificateGShape point := by
  have he := hinterior.2.1
  have hhalfMem : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hmono := lrCertificateQ_strictMonoOn.monotoneOn
    hhalfMem he heHalf
  have hQG := lrCertificateQ_E_le_GShape hinterior
  have hQ0 := lrLowerFaceQ0_le_Q
    (show (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num)
  have hQ0Eq : lrLowerFaceQ0 (1 / 2 : ℝ) =
      (3 * Real.log 2 + 1) / 8 := by
    unfold lrLowerFaceQ0
    rw [show (4 : ℝ) / (1 / 2) = 2 ^ 3 by norm_num,
      Real.log_pow]
    norm_num
    ring
  have hnumeric : (3079 / 8000 : ℝ) <
      (3 * Real.log 2 + 1) / 8 := by
    nlinarith [Real.log_two_gt_d9]
  rw [hQ0Eq] at hQ0
  exact hnumeric.trans_le (hQ0.trans (hmono.trans hQG))

/-- The radial estimates `R >= 127/128`, `4W/s > 299/320` turn any
positive upper bound for `H_d` into the common DA6 lower bound for `c0`. -/
lemma lrDeterminantC0_continuationTail_gt_of_Hd_lt
    {point : CertificatePoint} {U : ℝ}
    (hinterior : LRHighShapeInterior point)
    (hsSmall : point.s ≤ 1 / 128)
    (hU : 0 < U)
    (hHdUpper : lrDeterminantHd point < U) :
    3 / (10 * U) < lrDeterminantC0 point := by
  let R := lrCertificateR point
  let Wn := 4 * lrCertificateW point / point.s
  let Hd := lrDeterminantHd point
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hRLower : 127 / 128 ≤ R := by
    dsimp [R, lrCertificateR]
    nlinarith [hsSmall]
  have hRPos : 0 < R :=
    (by norm_num : (0 : ℝ) < 127 / 128).trans_le hRLower
  have hWnLower : 299 / 320 < Wn := by
    simpa [Wn] using lrCertificateW_normalized_gt_299_div_320 hs
  have hWnPos : 0 < Wn :=
    (by norm_num : (0 : ℝ) < 299 / 320).trans hWnLower
  have hprod : 9 / 10 < R * Wn := by
    have hleft : (127 / 128 : ℝ) * (299 / 320) <
        (127 / 128 : ℝ) * Wn :=
      mul_lt_mul_of_pos_left hWnLower (by norm_num)
    have hright : (127 / 128 : ℝ) * Wn ≤ R * Wn :=
      mul_le_mul_of_nonneg_right hRLower hWnPos.le
    norm_num at hleft ⊢
    exact (by norm_num : (9 / 10 : ℝ) < 37973 / 40960).trans
      (hleft.trans_le hright)
  have hHd : 0 < Hd := by
    simpa [Hd] using lrDeterminantHd_pos hinterior
  have hc0 : lrDeterminantC0 point = R * Wn / (3 * Hd) := by
    unfold lrDeterminantC0
    dsimp [R, Wn, Hd]
    field_simp [hinterior.1.1.ne']
  rw [hc0]
  rw [div_lt_div_iff₀
    (mul_pos (by norm_num) hU)
    (mul_pos (by norm_num) hHd)]
  have hleft : 9 * Hd < 9 * U :=
    mul_lt_mul_of_pos_left hHdUpper (by norm_num)
  have hright : 9 * U < 10 * (R * Wn) * U := by
    have hscaled := mul_lt_mul_of_pos_right hprod
      (mul_pos (by norm_num : (0 : ℝ) < 10) hU)
    nlinarith
  nlinarith

/-- The DA6 continuation theorem in the `e >= 1/2` branch. -/
theorem lrDeterminantNormalized_continuationTail_pos_largeE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsSmall : point.s ≤ 1 / 128)
    (heHalf : 1 / 2 ≤ lrCertificateE point) :
    0 < lrDeterminantNormalized
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrDeterminantPsi point / lrCertificateGShape point)
      (4 * lrDeterminantDelta point * lrCertificateW point /
        lrCertificateGShape point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point / lrCertificateGShape point) := by
  let L := Real.log (1 / point.s)
  let P := L + 33 / 4
  let G := lrCertificateGShape point
  let Hd := lrDeterminantHd point
  let Q := lrCertificateQ point.s
  let c0 := lrDeterminantC0 point
  let x := lrCertificateX point
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hL : 0 < L := by
    have harg : (128 : ℝ) ≤ 1 / point.s := by
      rw [le_div_iff₀ hs.1]
      nlinarith [hs.2]
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 128) harg
    have hlog128 : 0 < Real.log (128 : ℝ) :=
      Real.log_pos (by norm_num)
    exact hlog128.trans_le hlog
  have hP : 0 < P := by dsimp [P]; linarith
  have hHdUpper : Hd < P := by
    simpa [Hd, P, L] using
      lrDeterminantHd_continuationTail_upper_largeE hinterior hrelevant.1 hsSmall
  have hc0Lower : 3 / (10 * P) < c0 := by
    simpa [c0] using
      lrDeterminantC0_continuationTail_gt_of_Hd_lt hinterior hsSmall hP hHdUpper
  have hG : 3079 / 8000 < G := by
    simpa [G] using lrCertificateGShape_continuationTail_gt_largeE hinterior heHalf
  have hGPos : 0 < G := (by norm_num : (0 : ℝ) < 3079 / 8000).trans hG
  have hSP : point.s * P < 263 / 2560 := by
    simpa [P, L] using lrDeterminantContinuationTail_s_mul_log_add_lt hs
  have hcost : 25 * point.s / (32 * G) < 3 / (10 * P) := by
    rw [div_lt_div_iff₀
      (mul_pos (by norm_num) hGPos)
      (mul_pos (by norm_num) hP)]
    nlinarith
  have hQHd : Q / Hd < 9 * point.s / 32 := by
    simpa [Q, Hd] using lrDeterminantQ_div_Hd_continuationTail_lt hinterior hsSmall
  have hbracket : 0 < c0 -
      (point.s / 2 + Q / Hd) / G := by
    have hsum : point.s / 2 + Q / Hd < 25 * point.s / 32 := by
      nlinarith
    have hsumDiv : (point.s / 2 + Q / Hd) / G <
        25 * point.s / (32 * G) := by
      calc
        (point.s / 2 + Q / Hd) / G < (25 * point.s / 32) / G :=
          (div_lt_div_iff_of_pos_right hGPos).2 hsum
        _ = 25 * point.s / (32 * G) := by ring
    linarith [hc0Lower, hcost]
  have hxPos : 0 < x := by
    dsimp [x, lrCertificateX]
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hlower := lrDeterminantNormalized_continuationTail_lower hinterior hrelevant
  change x * (c0 - (point.s / 2 + Q / Hd) / G) ≤ _ at hlower
  exact (mul_pos hxPos hbracket).trans_le hlower

/-- Cleared singular positivity in the `e >= 1/2` continuation branch. -/
theorem lrDeterminantClearedSingular_continuationTail_pos_largeE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsSmall : point.s ≤ 1 / 128)
    (heHalf : 1 / 2 ≤ lrCertificateE point) :
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
    (lrDeterminantNormalized_continuationTail_pos_largeE
      hinterior hrelevant hsSmall heHalf)

/-- Sharper half-slope upper bound used when `v > 7/10`. -/
lemma lrLowHalfSlopeBase_lt_eleven_halves
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSeven : 7 / 10 ≤ v) :
    lrLowHalfSlopeBase v < 11 / 2 := by
  let p := lrFlowM v / 2
  let z := p / (2 - p)
  have hvPlus : 0 < 1 + v := by linarith [hv.1]
  have hpFormula : p = v / (2 * (1 + v)) := by
    unfold p lrFlowM
    field_simp [hvPlus.ne']
  have hpPos : 0 < p := by
    rw [hpFormula]
    exact div_pos hv.1 (mul_pos (by norm_num) hvPlus)
  have hpLower : 7 / 34 ≤ p := by
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
  have hquad : 0 <
      33 * p ^ 2 - 3169 / 34 * p + 67985 / 1156 := by
    nlinarith [hpUpper, sq_nonneg p]
  have hfactor : 0 ≤ (p - 7 / 34) *
      (33 * p ^ 2 - 3169 / 34 * p + 67985 / 1156) :=
    mul_nonneg (sub_nonneg.mpr hpLower) hquad.le
  have hpoly :
      12 * (1 - p) + p ^ 2 < 33 * p * (1 - p) * (2 - p) := by
    nlinarith [hfactor]
  have hden : 0 < 6 * (1 - p) * (2 - p) :=
    mul_pos (mul_pos (by norm_num) hpOne) hpTwo
  have hPadeBound :
      2 * (z + z ^ 3 / (3 * (1 - z ^ 2))) <
        11 / 2 * p ^ 2 := by
    rw [hPadeFormula, div_lt_iff₀ hden]
    have hscaled := mul_pos hpPos (sub_pos.mpr hpoly)
    nlinarith
  unfold lrLowHalfSlopeBase
  change -Real.log (1 - p) / p ^ 2 < 11 / 2
  rw [div_lt_iff₀ (sq_pos_of_pos hpPos)]
  exact hnegLog.trans_lt hPadeBound

/-- The low-entropy branch forces `v > 7/10`. -/
lemma lrCertificateV_continuationTail_gt_seven_tenths
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (heHalf : lrCertificateE point ≤ 1 / 2) :
    7 / 10 < lrCertificateV point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hxLe : lrCertificateX point ≤ 1 := by
    unfold lrCertificateX
    exact sub_le_self _ (mul_nonneg hinterior.2.2.1.le hinterior.2.1.1.le)
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point := by
    unfold lrCertificateV
    exact Real.sq_sqrt
      (div_nonneg (sub_nonneg.mpr hinterior.2.1.2.le) hxPos.le)
  have hratio : (1 / 2 : ℝ) ≤
      (1 - lrCertificateE point) / lrCertificateX point := by
    rw [le_div_iff₀ hxPos]
    nlinarith
  rw [← hvSq] at hratio
  nlinarith [hv.1]

/-- Continuation-tail upper bound for `H_d` in the branch `e <= 1/2`. -/
lemma lrDeterminantHd_continuationTail_upper_smallE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hsSmall : point.s ≤ 1 / 128)
    (heHalf : lrCertificateE point ≤ 1 / 2) :
    lrDeterminantHd point < Real.log (1 / point.s) + 36 / 7 := by
  let L := Real.log (1 / point.s)
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hs16 : point.s ∈ Ioc (0 : ℝ) (1 / 16 : ℝ) :=
    ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hv := lrCertificateV_mem_Ioo hinterior
  have hvSeven := lrCertificateV_continuationTail_gt_seven_tenths hinterior heHalf
  have hbase := lrLowHalfSlopeBase_lt_eleven_halves hv hvSeven.le
  have hmul := lrDeterminantContinuationTail_mul_log_four_upper hs
  have hlogSplit : Real.log (4 / point.s) = L + 2 * Real.log 2 := by
    dsimp [L]
    rw [show 4 / point.s = 4 * (1 / point.s) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (one_div_ne_zero hs.1.ne'),
      show Real.log 4 = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num]
    ring
  have hQ := lrCertificateQ_upper_sixteenth hs16
  rw [hlogSplit] at hQ
  have hQscaled : 4 * lrCertificateQ point.s / point.s ≤
      (1 + 4 * point.s / 9) * (L + 2 * Real.log 2) + 1 := by
    rw [div_le_iff₀ hs.1]
    nlinarith
  rw [lrDeterminantHd_eq_continuationTail hinterior]
  dsimp [L] at hQscaled hmul ⊢
  nlinarith [Real.log_two_gt_d9]

/-- Entropy reserve in the `e <= 1/2` branch. -/
lemma lrCertificateGShape_continuationTail_lower_smallE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hk : 32 ≤ point.k) :
    8 * point.s *
        (Real.log (1 / point.s) - 3 * Real.log 2 + 1) ≤
      lrCertificateGShape point := by
  have hs := hinterior.1
  have he := hinterior.2.1
  have h32E : 32 * point.s ≤ lrCertificateE point := by
    unfold lrCertificateE
    nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hk)]
  have h32Mem : 32 * point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos (by norm_num) hs.1, h32E.trans_lt he.2⟩
  have hQMono := lrCertificateQ_strictMonoOn.monotoneOn
    h32Mem he h32E
  have hQ0 := lrLowerFaceQ0_le_Q
    (show 32 * point.s ∈ Ioc (0 : ℝ) 1 from
      ⟨h32Mem.1, h32Mem.2.le⟩)
  have hQG := lrCertificateQ_E_le_GShape hinterior
  have hlogScale :
      Real.log (4 / (32 * point.s)) =
        Real.log (1 / point.s) - 3 * Real.log 2 := by
    rw [show 4 / (32 * point.s) = (1 / point.s) / 8 by
      field_simp [hs.1.ne']
      norm_num,
      Real.log_div (one_div_ne_zero hs.1.ne')
        (by norm_num : (8 : ℝ) ≠ 0),
      show Real.log 8 = 3 * Real.log 2 by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num]
  have hQ0Eq : lrLowerFaceQ0 (32 * point.s) =
      8 * point.s *
        (Real.log (1 / point.s) - 3 * Real.log 2 + 1) := by
    unfold lrLowerFaceQ0
    rw [hlogScale]
    ring
  rw [← hQ0Eq]
  exact hQ0.trans (hQMono.trans hQG)

/-- Audited logarithmic ratio for the `e <= 1/2` branch. -/
lemma lrDeterminantContinuationTail_log_ratio_smallE
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ)) :
    (Real.log (1 / s) + 36 / 7) /
        (Real.log (1 / s) - 3 * Real.log 2 + 1) <
      17575 / 6601 := by
  let L := Real.log (1 / s)
  let P := L + 36 / 7
  let D := L - 3 * Real.log 2 + 1
  have harg : (128 : ℝ) ≤ 1 / s := by
    rw [le_div_iff₀ hs.1]
    nlinarith [hs.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 128) harg
  have hpow : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hL : 7 * Real.log 2 ≤ L := by simpa [L, hpow] using hlog
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [Real.log_two_gt_d9]
  change P / D < 17575 / 6601
  rw [div_lt_iff₀ hD]
  dsimp [P, D]
  nlinarith [Real.log_two_gt_d9]

/-- The DA6 continuation theorem in the `e <= 1/2` branch. -/
theorem lrDeterminantNormalized_continuationTail_pos_smallE
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsSmall : point.s ≤ 1 / 128)
    (hk : 32 ≤ point.k)
    (heHalf : lrCertificateE point ≤ 1 / 2) :
    0 < lrDeterminantNormalized
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrDeterminantPsi point / lrCertificateGShape point)
      (4 * lrDeterminantDelta point * lrCertificateW point /
        lrCertificateGShape point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point / lrCertificateGShape point) := by
  let L := Real.log (1 / point.s)
  let P := L + 36 / 7
  let D := L - 3 * Real.log 2 + 1
  let G := lrCertificateGShape point
  let Hd := lrDeterminantHd point
  let Q := lrCertificateQ point.s
  let c0 := lrDeterminantC0 point
  let x := lrCertificateX point
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ) :=
    ⟨hinterior.1.1, hsSmall⟩
  have harg : (128 : ℝ) ≤ 1 / point.s := by
    rw [le_div_iff₀ hs.1]
    nlinarith [hs.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 128) harg
  have hpow : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hL : 7 * Real.log 2 ≤ L := by simpa [L, hpow] using hlog
  have hP : 0 < P := by
    dsimp [P]
    nlinarith [Real.log_two_gt_d9]
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [Real.log_two_gt_d9]
  have hHdUpper : Hd < P := by
    simpa [Hd, P, L] using
      lrDeterminantHd_continuationTail_upper_smallE hinterior hsSmall heHalf
  have hc0Lower : 3 / (10 * P) < c0 := by
    simpa [c0] using
      lrDeterminantC0_continuationTail_gt_of_Hd_lt hinterior hsSmall hP hHdUpper
  have hGPos : 0 < G := by
    simpa [G] using lrCertificateGShape_pos hinterior
  have hGLower : 8 * point.s * D ≤ G := by
    simpa [D, L, G] using lrCertificateGShape_continuationTail_lower_smallE hinterior hk
  have hratio : P / D < 17575 / 6601 := by
    simpa [P, D, L] using lrDeterminantContinuationTail_log_ratio_smallE hs
  have hratioCoarse : 250 * P < 768 * D := by
    rw [div_lt_iff₀ hD] at hratio
    nlinarith
  have hcostFirst : 25 * point.s / (32 * G) ≤ 25 / (256 * D) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hGPos)
      (mul_pos (by norm_num) hD)]
    have hscaled := mul_le_mul_of_nonneg_left hGLower (by norm_num : (0 : ℝ) ≤ 800)
    nlinarith
  have hcostSecond : 25 / (256 * D) < 3 / (10 * P) := by
    rw [div_lt_div_iff₀
      (mul_pos (by norm_num) hD)
      (mul_pos (by norm_num) hP)]
    nlinarith [hratioCoarse]
  have hQHd : Q / Hd < 9 * point.s / 32 := by
    simpa [Q, Hd] using lrDeterminantQ_div_Hd_continuationTail_lt hinterior hsSmall
  have hbracket : 0 < c0 -
      (point.s / 2 + Q / Hd) / G := by
    have hsum : point.s / 2 + Q / Hd < 25 * point.s / 32 := by
      nlinarith
    have hsumDiv : (point.s / 2 + Q / Hd) / G <
        25 * point.s / (32 * G) := by
      calc
        (point.s / 2 + Q / Hd) / G < (25 * point.s / 32) / G :=
          (div_lt_div_iff_of_pos_right hGPos).2 hsum
        _ = 25 * point.s / (32 * G) := by ring
    linarith [hc0Lower, hcostFirst.trans_lt hcostSecond]
  have hxPos : 0 < x := by
    dsimp [x, lrCertificateX]
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    linarith
  have hlower := lrDeterminantNormalized_continuationTail_lower hinterior hrelevant
  change x * (c0 - (point.s / 2 + Q / Hd) / G) ≤ _ at hlower
  exact (mul_pos hxPos hbracket).trans_le hlower

/-- Full normalized continuation theorem, combining the two entropy cases. -/
theorem lrDeterminantNormalized_continuationTail_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsSmall : point.s ≤ 1 / 128)
    (hk : 32 ≤ point.k) :
    0 < lrDeterminantNormalized
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrDeterminantPsi point / lrCertificateGShape point)
      (4 * lrDeterminantDelta point * lrCertificateW point /
        lrCertificateGShape point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point / lrCertificateGShape point) := by
  rcases le_total (lrCertificateE point) (1 / 2) with heSmall | heLarge
  · exact lrDeterminantNormalized_continuationTail_pos_smallE
      hinterior hrelevant hsSmall hk heSmall
  · exact lrDeterminantNormalized_continuationTail_pos_largeE
      hinterior hrelevant hsSmall heLarge

/-- Full cleared-singular continuation theorem. -/
theorem lrDeterminantClearedSingular_continuationTail_pos
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsSmall : point.s ≤ 1 / 128)
    (hk : 32 ≤ point.k) :
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
    (lrDeterminantNormalized_continuationTail_pos hinterior hrelevant hsSmall hk)

/-- Pointwise admitted-target version suitable for region assembly. -/
theorem lrDeterminantAdmittedTarget_continuationTail
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsSmall : point.s ≤ 1 / 128)
    (hk : 32 ≤ point.k) :
    LRDeterminantAdmittedTarget point := by
  right
  exact (lrDeterminantClearedSingular_continuationTail_pos hinterior hrelevant hsSmall hk).le

/-- The analytic continuation tail supplies its determinant-ledger row. -/
theorem lrDeterminantTailRegion_certificate :
    LRDeterminantRegionCertificateTheorem LRDeterminantTailRegion := by
  intro point hinterior hrelevant hregion
  exact lrDeterminantAdmittedTarget_continuationTail
    hinterior hrelevant hregion.1 hregion.2

end CourtadeKumar
