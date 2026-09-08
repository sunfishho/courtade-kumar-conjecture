import InformationTheory.CourtadeKumar.AnalyticExtension.DirectVBounds
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryAnalytic

/-! Exact cancellation of the channel restoration cost for direct V. -/
open Set
namespace CourtadeKumar.LRLowRatioDirectV

noncomputable def epsilonEntropy : ℝ := 1 / 1000

lemma omega_gap_identity {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    lrLowerFaceOmegaQ0 p.s (lrCertificateE p) - lrLowerFaceOmegaQ0 p.s 0 =
      -lrCertificateE p / 4 *
        (p.s + Real.log ((1 + (1 - p.s) * p.k) / p.k)) := by
  have hk0 : 0 < p.k := by linarith [hk.1, hi.1.1]
  rw [show lrCertificateE p = p.s * p.k by rfl,
    lrLowerFaceOmegaQ0_sk_eq hi.1 hk0 hi.2.1.2,
    lrLowerFaceOmegaQ0_zero hi.1.1]
  ring

lemma q0Core_eq_frozen_add {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    q0Core p = lrLowRatioNormalization p * frozen p +
      lrCertificateD p * lrSmallSBridgeQ0DeltaG p +
      (lrCertificateBFlow p + lrCertificateD p) * lrLowRatioQ0DeltaOmega p := by
  unfold q0Core
  rw [lrLowRatioQ0G_eq_frozen_add_delta,
    lrLowRatioQ0Omega_eq_frozen_add_delta,
    lrLowRatioQ0FrozenG_eq_normalized hi hk,
    lrLowRatioQ0FrozenOmega_eq_normalized hi hk]
  unfold frozen
  ring

lemma q0Core_grouped {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    q0Core p = lrLowRatioNormalization p * frozen p +
      lrCertificateD p * lrCertificateG0 (lrCertificateV p) +
      lrLowRatioBWeight p * (lrCertificateE p / 4 * restorationCoefficient p) +
      lrLowRatioKappa p *
        (lrCertificateD p * lrLowerFaceQ0 (lrCertificateE p) +
          (lrCertificateBFlow p + lrCertificateD p) *
            lrLowerFaceOmegaQ0 p.s (lrCertificateE p)) := by
  have hinner :
      lrCertificateD p * lrLowerFaceQ0 (lrCertificateE p) +
        (lrCertificateBFlow p + lrCertificateD p) *
          (lrLowerFaceOmegaQ0 p.s (lrCertificateE p) - lrLowerFaceOmegaQ0 p.s 0) =
      lrCertificateE p / 4 * restorationCoefficient p := by
    rw [omega_gap_identity hi hk]
    unfold lrLowerFaceQ0 restorationCoefficient
    ring
  rw [q0Core_eq_frozen_add hi hk, lrLowRatioQ0DeltaOmega_formula hi, ← hinner]
  unfold lrSmallSBridgeQ0DeltaG lrLowRatioKappa lrLowRatioAWeight
  ring

/-- Keeping the exact D makes the adverse q0 changes pay for themselves. -/
lemma q0_restoration {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) :
    lrLowRatioNormalization p * frozen p ≤ q0Core p := by
  let D := lrCertificateD p
  let B := lrCertificateBFlow p
  let e := lrCertificateE p
  let v := lrCertificateV p
  let d := 1 - v
  let b := lrLowRatioBWeight p
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have he0 : 0 ≤ e := hi.2.1.1.le
  have hd0 : 0 ≤ d := sub_nonneg.mpr hv.2.le
  have hD0 : 0 ≤ D := by linarith [d_one_le hi hk hs]
  have hB0 : 0 ≤ B := (lrCertificateBFlow_pos hi).le
  have hgap : d ≤ (51 / 100 : ℝ) * e := radial_gap hi hk hs
  have hg0 : -(3 / 10 : ℝ) * d ^ 2 ≤ lrCertificateG0 v :=
    g0_lower ⟨v_near_one hi hk hs, hv.2.le⟩
  have hbLower : d ≤ b := by
    dsimp [b]
    rw [(lrLowRatio_weight_identities hi).2.1,
      le_div_iff₀ (by linarith [hv.1] : 0 < 1 + lrCertificateV p)]
    change d * (1 + v) ≤ 2 * d
    dsimp [d]
    nlinarith
  have hb0 : 0 ≤ b := hd0.trans hbLower
  have hC : (63 / 100 : ℝ) * D ≤ restorationCoefficient p :=
    restorationCoefficient_lower hi hk hs
  have hpayLower :
      d * (e / 4 * ((63 / 100 : ℝ) * D)) ≤
        b * (e / 4 * restorationCoefficient p) := by
    exact mul_le_mul hbLower
      (mul_le_mul_of_nonneg_left hC (div_nonneg he0 (by norm_num)))
      (mul_nonneg (div_nonneg he0 (by norm_num)) (mul_nonneg (by norm_num) hD0)) hb0
  have hG := mul_le_mul_of_nonneg_left hg0 hD0
  have hgapScaled := mul_le_mul_of_nonneg_left hgap (mul_nonneg hD0 hd0)
  have hproduct := mul_nonneg hD0 (mul_nonneg he0 hd0)
  have hmain : 0 ≤ D * lrCertificateG0 v +
      b * (e / 4 * restorationCoefficient p) := by
    nlinarith
  have hQ0 := lrLowerFaceQ0_nonneg_of_mem ⟨hi.2.1.1, hi.2.1.2.le⟩
  have hOmega := lrLowerFaceOmegaQ0_nonneg hi.1 hi.2.1
  have hkappa := (kappa_bounds hi hk hs).1
  have hrest : 0 ≤ lrLowRatioKappa p *
      (D * lrLowerFaceQ0 e + (B + D) * lrLowerFaceOmegaQ0 p.s e) :=
    mul_nonneg hkappa (add_nonneg (mul_nonneg hD0 hQ0)
      (mul_nonneg (add_nonneg hB0 hD0) hOmega))
  rw [q0Core_grouped hi hk]
  dsimp [D, B, e, v, b] at hmain hrest
  linarith

lemma entropy_budget_envelope {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    (4 / 21 : ℝ) * (Real.log (1 / s) + 3) * s ^ 4 *
      (Real.log (1 / s) + 2 * Real.log 2) < epsilonEntropy := by
  let lam := Real.log 2
  let L := Real.log (1 / s)
  have hlam : lam < (7 / 10 : ℝ) := Real.log_two_lt_d9.trans (by norm_num)
  have hlam0 : 0 < lam := Real.log_pos (by norm_num)
  have hlogEnd : Real.log (4 / (1 / 8 : ℝ)) = 5 * lam := by
    rw [show (4 / (1 / 8 : ℝ)) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num [lam]
  have hendpoint : 1 ≤ Real.log (4 / (1 / 8 : ℝ)) := by
    rw [hlogEnd]
    dsimp [lam]
    nlinarith [Real.log_two_gt_d9]
  have hs8 : s ≤ (1 / 8 : ℝ) := hs.2.trans (by norm_num)
  have hmul := mul_log_four_div_le_endpoint hs.1 (by norm_num : (0 : ℝ) < 1 / 8) hs8 hendpoint
  rw [hlogEnd, lrLowRatio_log_four_div_split hs.1] at hmul
  have hL := log_lower hs
  have hL0 : 0 < L := by dsimp [L]; nlinarith
  have hlinear := mul_le_mul_of_nonneg_right hs8
    (show 0 ≤ 3 - 2 * lam by linarith)
  have h3 : s * (L + 3) < (2 / 3 : ℝ) := by
    dsimp [L, lam] at *
    nlinarith
  have h2 : s * (L + 2 * lam) < (1 / 2 : ℝ) := by
    dsimp [L, lam] at *
    nlinarith
  have hprod := mul_lt_mul_of_pos' h3 h2
    (mul_pos hs.1 (by linarith : 0 < L + 2 * lam)) (by norm_num : (0 : ℝ) < 2 / 3)
  have hsSq : s ^ 2 ≤ (1 / 100 : ℝ) := by nlinarith [hs.1, hs.2]
  have hscaled := mul_lt_mul_of_pos_left hprod (sq_pos_of_pos hs.1)
  unfold epsilonEntropy
  change (4 / 21 : ℝ) * (L + 3) * s ^ 4 * (L + 2 * lam) < 1 / 1000
  nlinarith

lemma r0Omega_lower
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 10) :
    -lrLowRatioKappa point * point.s * lrLowerFaceR0Prime point.s ≤
      lrLowRatioR0Omega point := by
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
  have hPW : (1 + 1 / v) * w ≤
      lrLowerFacePWR0 point.s point.k point.chi v := by
    unfold lrLowerFacePWR0
    have hadd := add_le_add (by simpa [w] using hY) hEDiv
    convert hadd using 1
    field_simp [hv.1.ne']
    ring
  have hkId := (lrLowRatio_weight_identities hinterior).2.2
  have hcoeff :
      1 + 1 / v - 4 / (1 + v) = lrLowRatioKappa point := by
    rw [hkId]
    dsimp [v]
    field_simp [hv.1.ne', (by linarith [hv.1] : 1 + lrCertificateV point ≠ 0)]
    ring
  have hOmegaBase : lrLowRatioKappa point * w ≤
      lrLowRatioR0Omega point := by
    calc
      lrLowRatioKappa point * w =
          (1 + 1 / v) * w - 4 * w / (1 + v) := by
            rw [← hcoeff]
            ring
      _ ≤ lrLowerFacePWR0 point.s point.k point.chi v -
          4 * w / (1 + v) := sub_le_sub_right hPW _
      _ = lrLowRatioR0Omega point := by
        unfold lrLowRatioR0Omega
        simp only [v, w]
  have hwLower := lrLowerFaceOmegaR0_zero_lower hs
  have hk0 := (kappa_bounds hinterior hregion hsSmall).1
  have hscaled := mul_le_mul_of_nonneg_left hwLower hk0
  have hlower :
      -lrLowRatioKappa point * point.s * lrLowerFaceR0Prime point.s ≤
        lrLowRatioKappa point * w := by
    calc
      -lrLowRatioKappa point * point.s * lrLowerFaceR0Prime point.s =
          lrLowRatioKappa point *
            (-point.s * lrLowerFaceR0Prime point.s) := by ring
      _ ≤ lrLowRatioKappa point * w := hscaled
  exact hlower.trans hOmegaBase

lemma r0_restoration
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantLowRatioRegion point)
    (hsSmall : point.s ≤ 1 / 10) :
    -lrLowRatioNormalization point * epsilonEntropy <
      r0Core point := by
  let L := lrLowRatioLogScale point
  let A := L + 3
  let C := L + 2 * Real.log 2
  let e := lrCertificateE point
  let n := lrLowRatioNormalization point
  let D1 := lrCertificateD point
  let B1 := lrCertificateBFlow point + lrCertificateD point
  let kap := lrLowRatioKappa point
  let rp := lrLowerFaceR0Prime point.s
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 10) :=
    ⟨hinterior.1.1, hsSmall⟩
  have hs0 : 0 ≤ point.s := hs.1.le
  have hLraw := log_lower hs
  have hL : 3 * Real.log 2 + 1 / 5 ≤ L := by
    simpa [L, lrLowRatioLogScale] using hLraw
  have hlam0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by dsimp [A]; nlinarith
  have hC0 : 0 ≤ C := by dsimp [C]; nlinarith
  have he0 : 0 ≤ e := by simpa [e] using hinterior.2.1.1.le
  have hn0 : 0 < n := by
    simpa [n] using lrLowRatioNormalization_pos hinterior
  have hD0 : 0 ≤ D1 := by
    simpa [D1] using (show 0 ≤ lrCertificateD point from by linarith [d_one_le hinterior hregion hsSmall])
  have hB0 : 0 ≤ lrCertificateBFlow point :=
    (lrCertificateBFlow_pos hinterior).le
  have hB10 : 0 ≤ B1 := by dsimp [B1]; linarith
  have hB1Upper : B1 ≤ A := by
    simpa [B1, A, L] using
      b_add_d_upper hinterior hregion hsSmall
  have hweights := kappa_bounds hinterior hregion hsSmall
  have hkap0 : 0 ≤ kap := by simpa [kap] using hweights.1
  have hkapUpper : kap ≤ (1 / 7 : ℝ) * e ^ 2 := by
    simpa [kap, e] using hweights.2
  have hrp0 : 0 ≤ rp := by
    simpa [rp] using lrLowerFaceR0Prime_nonneg hinterior.1
  have hsTenth : point.s ∈ Ioc (0 : ℝ) (1 / 10) :=
    ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hrpUpper0 := LRGapBudgetSEFourBoundaryAnalytic.lrLowerFaceR0Prime_upper_tenth hsTenth
  have hlogSplit := lrLowRatio_log_four_div_split hs.1
  have hrpUpper : rp ≤ point.s / 3 * C := by
    dsimp [rp, C, L]
    unfold lrLowRatioLogScale
    rw [← hlogSplit]
    exact hrpUpper0
  have hrpBound0 : 0 ≤ point.s / 3 * C :=
    mul_nonneg (div_nonneg hs0 (by norm_num)) hC0
  have hGr : 0 ≤ lrSmallSBridgeR0G point :=
    lrLowRatioR0G_nonnegative hinterior
  have hOmega : -kap * point.s * rp ≤ lrLowRatioR0Omega point := by
    simpa [kap, rp] using
      r0Omega_lower hinterior hregion hsSmall
  have hDGr : 0 ≤ D1 * lrSmallSBridgeR0G point :=
    mul_nonneg hD0 hGr
  have hBOmega := mul_le_mul_of_nonneg_left hOmega hB10
  have hcoreLower : -(B1 * kap * point.s * rp) ≤
      r0Core point := by
    calc
      -(B1 * kap * point.s * rp) =
          B1 * (-kap * point.s * rp) := by ring
      _ ≤ B1 * lrLowRatioR0Omega point := hBOmega
      _ ≤ D1 * lrSmallSBridgeR0G point +
          B1 * lrLowRatioR0Omega point := le_add_of_nonneg_left hDGr
      _ = r0Core point := by
        simp [D1, B1, r0Core]
  have hBK : B1 * kap ≤ A * ((1 / 7 : ℝ) * e ^ 2) :=
    mul_le_mul hB1Upper hkapUpper hkap0 hA0
  have hBK0 : 0 ≤ B1 * kap := mul_nonneg hB10 hkap0
  have hBKUpper0 : 0 ≤ A * ((1 / 7 : ℝ) * e ^ 2) :=
    mul_nonneg hA0 (mul_nonneg (by norm_num) (sq_nonneg e))
  have hBKs : B1 * kap * point.s ≤
      A * ((1 / 7 : ℝ) * e ^ 2) * point.s :=
    mul_le_mul_of_nonneg_right hBK hs0
  have hBKs0 : 0 ≤ B1 * kap * point.s := mul_nonneg hBK0 hs0
  have hBKsUpper0 : 0 ≤ A * ((1 / 7 : ℝ) * e ^ 2) * point.s :=
    mul_nonneg hBKUpper0 hs0
  have hprimeStep : B1 * kap * point.s * rp ≤
      B1 * kap * point.s * (point.s / 3 * C) :=
    mul_le_mul_of_nonneg_left hrpUpper hBKs0
  have hcoefficientStep :
      B1 * kap * point.s * (point.s / 3 * C) ≤
        A * ((1 / 7 : ℝ) * e ^ 2) * point.s * (point.s / 3 * C) :=
    mul_le_mul_of_nonneg_right hBKs hrpBound0
  have hcostUpper : B1 * kap * point.s * rp ≤
      (1 / 21 : ℝ) * A * e ^ 2 * point.s ^ 2 * C := by
    calc
      B1 * kap * point.s * rp ≤
          B1 * kap * point.s * (point.s / 3 * C) := hprimeStep
      _ ≤ A * ((1 / 7 : ℝ) * e ^ 2) * point.s * (point.s / 3 * C) :=
        hcoefficientStep
      _ = (1 / 21 : ℝ) * A * e ^ 2 * point.s ^ 2 * C := by ring
  have heScale : e ^ 2 ≤ 4 * point.s ^ 2 * n := by
    simpa [e, n] using
      lrLowRatio_e_sq_le_four_s_sq_mul_normalization hinterior hregion
  have hfactor0 : 0 ≤ (1 / 21 : ℝ) * A * point.s ^ 2 * C :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hA0) (sq_nonneg point.s)) hC0
  have hscale := mul_le_mul_of_nonneg_right heScale hfactor0
  have hrawScale :
      (1 / 21 : ℝ) * A * e ^ 2 * point.s ^ 2 * C ≤
        n * ((4 / 21 : ℝ) * A * point.s ^ 4 * C) := by
    calc
      (1 / 21 : ℝ) * A * e ^ 2 * point.s ^ 2 * C =
          e ^ 2 * ((1 / 21 : ℝ) * A * point.s ^ 2 * C) := by ring
      _ ≤ (4 * point.s ^ 2 * n) *
          ((1 / 21 : ℝ) * A * point.s ^ 2 * C) := hscale
      _ = n * ((4 / 21 : ℝ) * A * point.s ^ 4 * C) := by ring
  have hbudget := entropy_budget_envelope hs
  have hbudget' : (4 / 21 : ℝ) * A * point.s ^ 4 * C <
      epsilonEntropy := by
    simpa [A, C, L, lrLowRatioLogScale] using hbudget
  have hbudgetScaled :
      n * ((4 / 21 : ℝ) * A * point.s ^ 4 * C) <
        n * epsilonEntropy :=
    mul_lt_mul_of_pos_left hbudget' hn0
  have hcost : B1 * kap * point.s * rp <
      n * epsilonEntropy :=
    (hcostUpper.trans hrawScale).trans_lt hbudgetScaled
  change -n * epsilonEntropy <
    r0Core point
  nlinarith

end CourtadeKumar.LRLowRatioDirectV
