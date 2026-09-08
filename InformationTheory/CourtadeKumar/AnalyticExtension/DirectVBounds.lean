import InformationTheory.CourtadeKumar.AnalyticExtension.DirectVRadial

/-! Frozen logarithmic core and cancellation coefficients for exact direct V. -/
open Set
namespace CourtadeKumar.LRLowRatioDirectV

noncomputable def outerRemainder (p : CertificatePoint) : ℝ :=
  Real.log (1 + (1 - p.s) * p.k)
noncomputable def frozen (p : CertificatePoint) : ℝ :=
  lrCertificateD p * lrLowRatioP p +
    lrCertificateBFlow p * (lrLowRatioP p - lrLowRatioG p)
noncomputable def q0Core (p : CertificatePoint) : ℝ :=
  lrCertificateD p * lrSmallSBridgeQ0G p +
    (lrCertificateBFlow p + lrCertificateD p) * lrLowRatioQ0Omega p
noncomputable def r0Core (p : CertificatePoint) : ℝ :=
  lrCertificateD p * lrSmallSBridgeR0G p +
    (lrCertificateBFlow p + lrCertificateD p) * lrLowRatioR0Omega p
noncomputable def restorationCoefficient (p : CertificatePoint) : ℝ :=
  lrCertificateD p * (Real.log (4 / lrCertificateE p) + 1) -
    (lrCertificateBFlow p + lrCertificateD p) *
      (p.s + Real.log ((1 + (1 - p.s) * p.k) / p.k))

lemma log_lower {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    3 * Real.log 2 + (1 / 5 : ℝ) ≤ Real.log (1 / s) := by
  have harg : (10 : ℝ) ≤ 1 / s := by rw [le_div_iff₀ hs.1]; nlinarith [hs.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 10) harg
  have hsmall := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  have hid : Real.log (10 : ℝ) = 3 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ 3 ≠ 0) (by norm_num : (5 / 4 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num
  rw [hid] at hlog
  norm_num at hsmall
  linarith

lemma outerRemainder_bounds {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    0 ≤ outerRemainder p ∧ outerRemainder p ≤ p.s := by
  have hk0 : 0 < p.k := by linarith [hk.1, hi.1.1]
  have hprod : 0 ≤ (1 - p.s) * p.k := mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk0.le
  have hprodUpper : (1 - p.s) * p.k ≤ p.s := by
    nlinarith [mul_nonneg hi.1.1.le hk0.le, hk.2]
  constructor
  · exact Real.log_nonneg (by linarith)
  · have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (1 - p.s) * p.k)
    change Real.log (1 + (1 - p.s) * p.k) ≤ p.s
    linarith

lemma d_identity {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    lrCertificateD p =
      (lrLowRatioLogScale p + lrLowRatioRho p + outerRemainder p) / 2 := by
  have hk0 : 0 < p.k := by linarith [hk.1, hi.1.1]
  have hnum : 0 < 1 + (1 - p.s) * p.k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk0.le]
  rw [lrCertificateD_eq_half_log_determinantY hi,
    lrLowRatio_determinantY_formula hi hk, Real.log_div hnum.ne' hk0.ne',
    lrLowRatio_log_k_identity hi hk]
  unfold outerRemainder
  ring

lemma d_lower {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    (lrLowRatioLogScale p + lrLowRatioRho p) / 2 ≤ lrCertificateD p := by
  rw [d_identity hi hk]
  linarith [(outerRemainder_bounds hi hk).1]

lemma d_one_le {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) : 1 ≤ lrCertificateD p := by
  have hL := log_lower ⟨hi.1.1, hs⟩
  have hD := d_lower hi hk
  have hrho := lrLowRatioRho_nonnegative hi hk
  unfold lrLowRatioLogScale at hD
  nlinarith [Real.log_two_gt_d9]

lemma b_add_d_upper {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) :
    lrCertificateBFlow p + lrCertificateD p ≤ lrLowRatioLogScale p + 3 := by
  have hD := d_identity hi hk
  have hb := lrLowRatio_B_upper hi
  have hrho := lrLowRatioRho_lt_two_log_two hi hk
  have ha := (outerRemainder_bounds hi hk).2
  nlinarith [Real.log_two_lt_d9]

lemma log_four_e {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    Real.log (4 / lrCertificateE p) =
      2 * lrLowRatioLogScale p + lrLowRatioRho p + 2 * Real.log 2 := by
  have hk0 : 0 < p.k := by linarith [hk.1, hi.1.1]
  have hLs : Real.log p.s = -lrLowRatioLogScale p := by
    unfold lrLowRatioLogScale
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hi.1.1.ne']
    simp
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hi.2.1.1.ne']
  rw [show lrCertificateE p = p.s * p.k by rfl,
    Real.log_mul hi.1.1.ne' hk0.ne', hLs, lrLowRatio_log_k_identity hi hk,
    lrSmallSBridge_log_four]
  ring

lemma outer_log_eq_two_d {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p) :
    Real.log ((1 + (1 - p.s) * p.k) / p.k) = 2 * lrCertificateD p := by
  rw [lrCertificateD_eq_half_log_determinantY hi, lrLowRatio_determinantY_formula hi hk]
  ring

lemma restorationCoefficient_lower {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) :
    (63 / 100 : ℝ) * lrCertificateD p ≤ restorationCoefficient p := by
  let D := lrCertificateD p
  let B := lrCertificateBFlow p
  let L := lrLowRatioLogScale p
  let a := outerRemainder p
  let lam := Real.log 2
  have hD1 : 1 ≤ D := d_one_le hi hk hs
  have hD0 : 0 ≤ D := by linarith
  have hB : B ≤ L / 2 + lam := lrLowRatio_B_upper hi
  have hrho := lrLowRatioRho_nonnegative hi hk
  have hDlow := d_lower hi hk
  have hBD : B ≤ D + lam := by dsimp [B, D, L, lam] at *; linarith
  have ha : a ≤ p.s := (outerRemainder_bounds hi hk).2
  have hlam : lam < (7 / 10 : ℝ) := Real.log_two_lt_d9.trans (by norm_num)
  have hlam0 : 0 ≤ lam := (Real.log_pos (by norm_num)).le
  have hcoef : 0 ≤ L + 2 * lam - 2 * B := by linarith
  have hpositive := mul_nonneg hD0 hcoef
  have hsa := mul_nonneg hD0 (sub_nonneg.mpr ha)
  have hid : restorationCoefficient p =
      D * (L + 2 * lam - 2 * B + 1 - p.s - a) - B * p.s := by
    unfold restorationCoefficient
    rw [log_four_e hi hk, outer_log_eq_two_d hi hk]
    have hd := d_identity hi hk
    dsimp [D, B, L, lam, a]
    nlinarith [hd]
  rw [hid]
  have hscaleB := mul_nonneg (sub_nonneg.mpr hBD) hi.1.1.le
  have hscaleS := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ 3 * D + lam by linarith)
  nlinarith

lemma frozen_scalar {s L lam w : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (hL : 3 * lam + 1 / 5 ≤ L)
    (hlam0 : 0 < lam) (hlam : lam < 7 / 10) (hw : w < 2 / 7) :
    (3 / 140 : ℝ) < L * (1 / 2 - 2 * s - w / 2) - lam * w - 2 * lam * s := by
  have hL0 : 0 ≤ L := by linarith
  have hcw := mul_nonneg (sub_nonneg.mpr hw.le)
    (show 0 ≤ L / 2 + lam by linarith)
  have hcs := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ 2 * L + 2 * lam by linarith)
  nlinarith

lemma frozen_margin {p : CertificatePoint}
    (hi : LRHighShapeInterior p) (hk : LRDeterminantLowRatioRegion p)
    (hs : p.s ≤ 1 / 10) : (3 / 140 : ℝ) < frozen p := by
  let L := lrLowRatioLogScale p
  let lam := Real.log 2
  let rho := lrLowRatioRho p
  let w := -lrSmallSBridgeQChi p.chi
  let D0 := (L + rho) / 2
  let P0 := L + 2 * lam + 1 - 2 * p.s
  let S0 := -L - rho - w - 2 * p.s
  let B0 := L / 2 + lam
  have hL : 3 * lam + 1 / 5 ≤ L := log_lower ⟨hi.1.1, hs⟩
  have hlam0 : 0 < lam := Real.log_pos (by norm_num)
  have hlam : lam < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hrho : 0 ≤ rho := lrLowRatioRho_nonnegative hi hk
  have hw : w < 2 / 7 := by
    have hq := lrSmallSBridgeQChi_lower ⟨hi.2.2.1.le, hi.2.2.2.le⟩
    dsimp [w]
    linarith
  have hD0 : 0 ≤ lrCertificateD p := by linarith [d_one_le hi hk hs]
  have hP00 : 0 ≤ P0 := by dsimp [P0]; nlinarith [hi.1.1.le]
  have hB00 : 0 ≤ B0 := by dsimp [B0]; nlinarith
  have hD := d_lower hi hk
  have hP := lrLowRatioP_lower hi hk
  have hS := lrLowRatioP_sub_G_lower hi hk
  have hSn := lrLowRatioP_sub_G_nonpositive hi hk
  have hB := lrLowRatio_B_upper hi
  have hDP : D0 * P0 ≤ lrCertificateD p * lrLowRatioP p :=
    mul_le_mul hD hP hP00 hD0
  have hS0 : S0 ≤ lrLowRatioP p - lrLowRatioG p := by
    dsimp [S0, w]
    linarith [hS]
  have hBS : B0 * S0 ≤ lrCertificateBFlow p * (lrLowRatioP p - lrLowRatioG p) := by
    exact (mul_le_mul_of_nonneg_left hS0 hB00).trans
      (mul_le_mul_of_nonpos_right hB hSn)
  have hscalar := frozen_scalar hi.1.1.le hs hL hlam0 hlam hw
  have hrhoTerm := mul_nonneg hrho (show 0 ≤ 1 / 2 - p.s by linarith)
  unfold frozen
  dsimp [D0, P0, S0, B0] at hDP hBS
  nlinarith

end CourtadeKumar.LRLowRatioDirectV
