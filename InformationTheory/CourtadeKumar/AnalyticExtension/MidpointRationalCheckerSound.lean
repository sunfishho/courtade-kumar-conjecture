import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalExprSound
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointEndpointBudget
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalCore

/-! Soundness of each exact-rational leaf for the original midpoint core.
Endpoint logs, interval denominators, signs, and payments are all checked. -/
namespace CourtadeKumar.LRMidpointReducedCertificate
open LRAnalyticMidpoint

lemma Leaf.endpoint_bounds {b : CertificateBox} {d : Leaf} {p : CertificatePoint}
    (hv : BoxValid b) (hp : b.Contains p)
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p)
    (hc : d.logC.check (4 / b.sHi) = true)
    (hal : d.logALo.check (1 + (1 - b.sHi) * b.kLo) = true)
    (hah : d.logAHi.check (1 + (1 - b.sLo) * b.kHi) = true)
    (hrl : d.logRatioLo.check (b.kLo / b.sHi) = true)
    (hrh : d.logRatioHi.check (b.kHi / b.sLo) = true)
    (ha : 0 ≤ d.logALo.lower ∧ d.logALo.lower ≤ 2) :
    d.bd.Contains (lrCertificateBFlow p - lrCertificateD p) ∧
      4 * entropyPayment p ≤ (d.payment b : ℝ) := by
  have hsl : (0 : ℝ) < b.sLo := by exact_mod_cast hv.1
  have hsh : (b.sHi : ℝ) ≤ 1 / 10 := by
    have hq : (10 : ℚ) * b.sHi ≤ 1 := by linarith [hv.2.2.1]
    have hcast : (10 : ℝ) * (b.sHi : ℝ) ≤ 1 := by exact_mod_cast hq
    linarith
  have hkl : (1 / 4 : ℝ) ≤ b.kLo := by
    have hq : (1 : ℚ) ≤ 4 * b.kLo := by linarith [hv.2.2.2.1]
    have hcast : (1 : ℝ) ≤ 4 * (b.kLo : ℝ) := by exact_mod_cast hq
    linarith
  have hkh : (b.kHi : ℝ) ≤ 4 := by exact_mod_cast hv.2.2.2.2.2.1
  have hsh0 : (0 : ℝ) < b.sHi := hi.1.1.trans_le hp.2.1
  have hkl0 : (0 : ℝ) < b.kLo := by linarith
  have hk : 0 < p.k := hkl0.trans_le hp.2.2.1
  have hkh0 : (0 : ℝ) < b.kHi := hk.trans_le hp.2.2.2.1
  have hs := hp.2.1.trans hsh
  have hk4 := hp.2.2.2.1.trans hkh
  have hClog := RoundedLog.sound hc
  have hALog := RoundedLog.sound hal
  have hAHiLog := RoundedLog.sound hah
  have hRLoLog := RoundedLog.sound hrl
  have hRHiLog := RoundedLog.sound hrh
  norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hClog hALog hAHiLog hRLoLog hRHiLog
  have hargLo : 1 + (1 - (b.sHi : ℝ)) * (b.kLo : ℝ) ≤
      1 + (1 - p.s) * p.k := by
    have h := mul_le_mul (sub_le_sub_left hp.2.1 1) hp.2.2.1 hkl0.le
      (sub_nonneg.mpr hi.1.2.le)
    linarith
  have hargHi : 1 + (1 - p.s) * p.k ≤
      1 + (1 - (b.sLo : ℝ)) * (b.kHi : ℝ) := by
    have h := mul_le_mul (sub_le_sub_left hp.1 1) hp.2.2.2.1 hk.le
      (show 0 ≤ 1 - (b.sLo : ℝ) by linarith [hp.1, hi.1.2])
    linarith
  have hargLo0 : 0 < 1 + (1 - (b.sHi : ℝ)) * (b.kLo : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (b.sHi : ℝ) by linarith) hkl0.le]
  have harg0 := hargLo0.trans_le hargLo
  have haLo : (d.logALo.lower : ℝ) ≤ Real.log (1 + (1 - p.s) * p.k) :=
    hALog.1.trans (Real.log_le_log hargLo0 hargLo)
  have haHi : Real.log (1 + (1 - p.s) * p.k) ≤ (d.logAHi.upper : ℝ) :=
    (Real.log_le_log harg0 hargHi).trans hAHiLog.2
  have hratioLo : (b.kLo : ℝ) / (b.sHi : ℝ) ≤ p.k / p.s :=
    (div_le_div_of_nonneg_right hp.2.2.1 hsh0.le).trans
      (div_le_div_of_nonneg_left hk.le hi.1.1 hp.2.1)
  have hratioHi : p.k / p.s ≤ (b.kHi : ℝ) / (b.sLo : ℝ) :=
    (div_le_div_of_nonneg_right hp.2.2.2.1 hi.1.1.le).trans
      (div_le_div_of_nonneg_left hkh0.le hsl hp.1)
  have hrLo : (d.logRatioLo.lower : ℝ) ≤ Real.log (p.k / p.s) :=
    hRLoLog.1.trans (Real.log_le_log (div_pos hkl0 hsh0) hratioLo)
  have hrHi : Real.log (p.k / p.s) ≤ (d.logRatioHi.upper : ℝ) :=
    (Real.log_le_log (div_pos hk hi.1.1) hratioHi).trans hRHiLog.2
  have hbd := endpoint_bd hi hr hs hk4 hrLo hrHi haLo haHi
  have haReal : (d.logALo.lower : ℝ) ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  have hpay := endpoint_payment hi hp.2.1 hsh haReal haLo hClog.2
  constructor
  · simpa [Leaf.bd, RationalEnclosure.Contains] using hbd
  · simpa [Leaf.payment] using hpay

noncomputable def values (p : CertificatePoint) (payment : ℝ) : Nat → ℝ
  | 0 => p.s
  | 1 => p.k
  | 2 => p.chi
  | 3 => lrCertificateBFlow p - lrCertificateD p
  | 4 => payment
  | _ => 0

lemma eval_u (p : CertificatePoint) (payment : ℝ) :
    uExpr.eval (values p payment) = rationalU p.s p.k p.chi := by
  simp [uExpr, alphaExpr, tExpr, Expr.eval, values, rationalU, rationalAlpha, rationalT]

lemma eval_lower (p : CertificatePoint) (payment : ℝ) :
    lowerExpr.eval (values p payment) =
      rationalLower p.s p.k p.chi (lrCertificateBFlow p - lrCertificateD p) payment := by
  simp [lowerExpr, hExpr, uExpr, dExpr, alphaExpr, tExpr, Expr.eval, values,
    rationalLower, rationalH, rationalU, rationalD, rationalAlpha, rationalT]

theorem Leaf.sound (b : CertificateBox) (d : Leaf) (hcheck : d.check b = true)
    (p : CertificatePoint) (hp : b.Contains p)
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p) :
    0 ≤ coreTarget p := by
  have hparts : BoxValid b ∧ d.logC.check (4 / b.sHi) = true ∧
      d.logALo.check (1 + (1 - b.sHi) * b.kLo) = true ∧
      d.logAHi.check (1 + (1 - b.sLo) * b.kHi) = true ∧
      d.logRatioLo.check (b.kLo / b.sHi) = true ∧
      d.logRatioHi.check (b.kHi / b.sLo) = true ∧
      (0 ≤ d.logALo.lower ∧ d.logALo.lower ≤ 2) ∧
      uExpr.valid (d.inputs b) = true ∧ 0 ≤ (uExpr.enclose (d.inputs b)).lower ∧
      lowerExpr.valid (d.inputs b) = true ∧ 0 ≤ (lowerExpr.enclose (d.inputs b)).lower := by
    simpa only [Leaf.check, Bool.and_eq_true, decide_eq_true_eq] using hcheck
  rcases hparts with ⟨hv, hc, hal, hah, hrl, hrh, ha, huValid, huLo, hlValid, hlLo⟩
  have hb := d.endpoint_bounds hv hp hi hr hc hal hah hrl hrh ha
  have henv : ∀ i, (d.inputs b i).Contains (values p (d.payment b : ℝ) i) := by
    intro i
    match i with
    | 0 => exact ⟨hp.1, hp.2.1⟩
    | 1 => exact ⟨hp.2.2.1, hp.2.2.2.1⟩
    | 2 => exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
    | 3 => exact hb.1
    | 4 => exact RationalEnclosure.contains_point (d.payment b)
    | _ + 5 => simpa [Leaf.inputs, values, Nat.add_comm] using RationalEnclosure.contains_point 0
  have hu := uExpr.sound henv huValid
  have hl := lowerExpr.sound henv hlValid
  rw [eval_u] at hu
  rw [eval_lower] at hl
  have hu0 : 0 ≤ rationalU p.s p.k p.chi :=
    (show (0 : ℝ) ≤ ((uExpr.enclose (d.inputs b)).lower : ℝ) by exact_mod_cast huLo).trans hu.1
  have hl0 : 0 ≤ rationalLower p.s p.k p.chi
      (lrCertificateBFlow p - lrCertificateD p) (d.payment b : ℝ) :=
    (show (0 : ℝ) ≤ ((lowerExpr.enclose (d.inputs b)).lower : ℝ) by exact_mod_cast hlLo).trans hl.1
  have h := rationalLower_le_core hi hr hu0 hb.2
  linarith

end CourtadeKumar.LRMidpointReducedCertificate
