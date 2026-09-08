import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantCheckerCore
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalExprSound
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantGap

/-! Exact endpoint witnesses enclose every input to the rational determinant. -/
namespace CourtadeKumar.LRDeterminantReducedCertificate
open LRMidpointReducedCertificate LRAnalyticDeterminant

noncomputable def values (p : CertificatePoint) (b : CertificateBox) (d : Leaf) : Nat → ℝ
  | 0 => p.s
  | 1 => p.k
  | 2 => p.chi
  | 3 => Real.log (4 / p.s)
  | 4 => (d.hCap b : ℝ)
  | 5 => lrCertificateBFlow p
  | 6 => (d.dLower b : ℝ)
  | 7 => (d.tangentPoint : ℝ)
  | 8 => (d.logTangent.upper : ℝ)
  | _ => 0

lemma Leaf.endpoint_bounds {b : CertificateBox} {d : Leaf} {p : CertificatePoint}
    (hv : BoxValid b) (hp : b.Contains p) (hi : LRHighShapeInterior p)
    (hcl : d.logCLo.check (4 / b.sHi) = true)
    (hch : d.logCHi.check (4 / b.sLo) = true)
    (hal : d.logALo.check (1 + (1 - b.sHi) * b.kLo) = true)
    (hah : d.logAHi.check (1 + (1 - b.sLo) * b.kHi) = true)
    (hd : d.logD.check ((1 + lowerY b) / 2) = true) :
    (∀ i, (d.inputs b i).Contains (values p b d i)) ∧
      (d.dLower b : ℝ) ≤ lrDeterminantD1 p ∧
      lrLowKIdealH (1 + (1 - p.s) * p.k) ≤ (d.hCap b : ℝ) ∧
      p.s ≤ 1 / 10 ∧ p.k ≤ 4 := by
  have hsl : (0 : ℝ) < b.sLo := by exact_mod_cast hv.1
  have hsh : (b.sHi : ℝ) ≤ 1 / 10 := by
    have hq : (10 : ℚ) * b.sHi ≤ 1 := by linarith [hv.2.2.1]
    have hr : (10 : ℝ) * (b.sHi : ℝ) ≤ 1 := by exact_mod_cast hq
    linarith
  have hkl : (0 : ℝ) < b.kLo := by exact_mod_cast hv.2.2.2.1
  have hkh : (b.kHi : ℝ) ≤ 4 := by exact_mod_cast hv.2.2.2.2.2.1
  have hsh0 : (0 : ℝ) < b.sHi := hi.1.1.trans_le hp.2.1
  have hk0 : 0 < p.k := hkl.trans_le hp.2.2.1
  have hkh0 : (0 : ℝ) < b.kHi := hk0.trans_le hp.2.2.2.1
  have hs := hp.2.1.trans hsh
  have hk := hp.2.2.2.1.trans hkh
  have hClo := RoundedLog.sound hcl
  have hChi := RoundedLog.sound hch
  have hAlo := RoundedLog.sound hal
  have hAhi := RoundedLog.sound hah
  have hDlog := RoundedLog.sound hd
  norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one] at hClo hChi hAlo hAhi hDlog
  have hCargLo : 4 / (b.sHi : ℝ) ≤ 4 / p.s :=
    div_le_div_of_nonneg_left (by norm_num) hi.1.1 hp.2.1
  have hCargHi : 4 / p.s ≤ 4 / (b.sLo : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hsl hp.1
  have hCL : (d.logCLo.lower : ℝ) ≤ Real.log (4 / p.s) :=
    hClo.1.trans (Real.log_le_log (div_pos (by norm_num) hsh0) hCargLo)
  have hCU : Real.log (4 / p.s) ≤ (d.logCHi.upper : ℝ) :=
    (Real.log_le_log (div_pos (by norm_num) hi.1.1) hCargHi).trans hChi.2
  let A := (1 - p.s) * p.k
  let aLo := (1 - (b.sHi : ℝ)) * (b.kLo : ℝ)
  let aHi := (1 - (b.sLo : ℝ)) * (b.kHi : ℝ)
  have hAl0 : 0 < aLo := mul_pos (by linarith) hkl
  have hAL : aLo ≤ A :=
    mul_le_mul (sub_le_sub_left hp.2.1 1) hp.2.2.1 hkl.le (sub_nonneg.mpr hi.1.2.le)
  have hAU : A ≤ aHi :=
    mul_le_mul (sub_le_sub_left hp.1 1) hp.2.2.2.1 hk0.le
      (by linarith [hp.1, hi.1.2] : 0 ≤ 1 - (b.sLo : ℝ))
  have hA0 : 0 < A := hAl0.trans_le hAL
  have haL : (d.logALo.lower : ℝ) ≤ Real.log (1 + A) :=
    hAlo.1.trans (Real.log_le_log (by linarith : 0 < 1 + aLo) (by linarith))
  have haU : Real.log (1 + A) ≤ (d.logAHi.upper : ℝ) :=
    (Real.log_le_log (by linarith : 0 < 1 + A) (by linarith : 1 + A ≤ 1 + aHi)).trans hAhi.2
  have hBetaL := LRAnalyticMidpoint.beta_lower hi hs hk
  have hvp := lrCertificateV_mem_Ioo hi
  have hBetaU : Real.log (1 + lrCertificateV p) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [hvp.1]) (by linarith [hvp.2])
  have hBform := LRAnalyticMidpoint.b_formula hi
  have hCform := lrLowRatio_log_four_div_split hi.1.1
  unfold lrLowRatioLogScale at hBform
  have hBL : (d.logCLo.lower : ℝ) / 2 - 7 / 10 + 6 / 11 - (d.logAHi.upper : ℝ) / 2 ≤
      lrCertificateBFlow p := by
    dsimp [A] at haU
    linarith [Real.log_two_lt_d9]
  have hBU : lrCertificateBFlow p ≤ (d.logCHi.upper : ℝ) / 2 - (d.logALo.lower : ℝ) / 2 := by
    dsimp [A] at haL
    linarith
  let Y : ℝ := (lowerY b : ℝ)
  have hYform : Y = 1 / (b.kHi : ℝ) + 1 - (b.sHi : ℝ) := by
    norm_num [Y, lowerY]
  have hY1 : 1 ≤ Y := by
    have hki : (1 / 4 : ℝ) ≤ 1 / (b.kHi : ℝ) := one_div_le_one_div_of_le hkh0 hkh
    rw [hYform]
    linarith
  have hYexact : lrDeterminantY p = 1 / p.k + 1 - p.s := by
    unfold lrDeterminantY lrCertificateB lrCertificateE
    field_simp [hi.1.1.ne', hk0.ne']
    ring
  have hYY : Y ≤ lrDeterminantY p := by
    have hki := one_div_le_one_div_of_le hk0 hp.2.2.2.1
    rw [hYform, hYexact]
    linarith [hp.2.1]
  have hmodel := (lrDA7DModel_finite_loss hY1 (sub_nonneg.mpr hYY)).1
  rw [show Y + (lrDeterminantY p - Y) = lrDeterminantY p by ring] at hmodel
  have hDL : (d.dLower b : ℝ) ≤ lrDA7DModel Y := by
    unfold Leaf.dLower lrDA7DModel
    norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one]
    change (d.logD.lower : ℝ) / 2 + (Y - 1) / (3 * Y + 1) ≤
      1 / 2 * Real.log ((1 + Y) / 2) + (Y - 1) / (3 * Y + 1)
    linarith [hDlog.1]
  have hdfinal : (d.dLower b : ℝ) ≤ lrDeterminantD1 p := hDL.trans hmodel
  have hH : lrLowKIdealH (1 + A) ≤ (d.hCap b : ℝ) := by
    have hlog0 : 0 ≤ Real.log (1 + A) := Real.log_nonneg (by linarith)
    have haU0 : 0 ≤ (d.logAHi.upper : ℝ) := hlog0.trans haU
    have hnum := mul_le_mul (show 1 + A ≤ 1 + aHi by linarith) haU hlog0 (by linarith : 0 ≤ 1 + aHi)
    have hquot := (div_le_div_of_nonneg_right hnum hA0.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by linarith : 0 ≤ 1 + aHi) haU0) hAl0 hAL)
    have h1 : lrLowKIdealH (1 + A) ≤ (1 + aHi) * (d.logAHi.upper : ℝ) / aLo := by
      unfold lrLowKIdealH
      rw [if_neg (by linarith : 1 + A ≠ 1)]
      simpa only [add_sub_cancel_left] using hquot
    have h2 : lrLowKIdealH (1 + A) ≤ 1 + aHi / 2 :=
      (h_one_add_upper hA0).trans (by linarith)
    have hmin := le_min h1 h2
    simpa [Leaf.hCap, aHi, aLo] using hmin
  refine ⟨?_, hdfinal, hH, hs, hk⟩
  intro i
  match i with
  | 0 => exact ⟨hp.1, hp.2.1⟩
  | 1 => exact ⟨hp.2.2.1, hp.2.2.2.1⟩
  | 2 => exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  | 3 => exact ⟨hCL, hCU⟩
  | 4 => exact RationalEnclosure.contains_point (d.hCap b)
  | 5 => simpa [Leaf.inputs, values, RationalEnclosure.Contains] using And.intro hBL hBU
  | 6 => exact RationalEnclosure.contains_point (d.dLower b)
  | 7 => exact RationalEnclosure.contains_point d.tangentPoint
  | 8 => exact RationalEnclosure.contains_point d.logTangent.upper
  | _ + 9 => simpa [Leaf.inputs, values, Nat.add_comm] using RationalEnclosure.contains_point 0

end CourtadeKumar.LRDeterminantReducedCertificate
