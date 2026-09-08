import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRestoration
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryAnalytic

/-! A sharp endpoint entropy payment, retaining the favorable logarithm
in r0(s)-s*r0'(s), for the entire near-endpoint midpoint domain. -/
open Set
namespace CourtadeKumar.LRAnalyticMidpoint

lemma omega_zero_p_formula {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    let p := lrLowerFaceP s
    lrLowerFaceOmegaR0 s 0 =
      (p ^ 2 * Real.log p - (1 - p) ^ 2 * Real.log (1 - p)) / (1 - 2 * p) -
        p * (1 - p) := by
  let p := lrLowerFaceP s
  have hg := lrLowerFaceP_geometry hs
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧ 1 - 2 * p = Real.sqrt (1 - s) ∧
    s = 4 * p * (1 - p) at hg
  have hW : lrLowerFaceOmegaR0 s 0 = lrLowerFaceR0 s - s * lrLowerFaceR0Prime s := by
    simp [lrLowerFaceOmegaR0, lrCertificateB]
  rw [hW, lrLowerFaceR0_eq_pFormula hs, lrLowerFaceR0Prime_eq_p hs]
  unfold lrLowerFaceR0PFormula
  simp only [Real.negMulLog_eq_neg]
  change p * -(p * Real.log p) + (1 - p) * -((1 - p) * Real.log (1 - p)) -
      p * (1 - p) - s * (((1 - p) * Real.log (1 - p) - p * Real.log p) /
        (2 * (1 - 2 * p))) =
      (p ^ 2 * Real.log p - (1 - p) ^ 2 * Real.log (1 - p)) / (1 - 2 * p) - p * (1 - p)
  rw [hg.2.2]
  field_simp [show 1 - 2 * p ≠ 0 by linarith [hg.1.2],
    show 1 - p * 2 ≠ 0 by linarith [hg.1.2]]
  ring

/-- This bounds the actual endpoint remainder, rather than dropping r0(s). -/
theorem omega_zero_lower {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    -(s ^ 2 / 14 * Real.log (4 / s)) ≤ lrLowerFaceOmegaR0 s 0 := by
  have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  let p := lrLowerFaceP s
  let z := Real.sqrt (1 - s)
  have hg := lrLowerFaceP_geometry hs1
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧ 1 - 2 * p = z ∧ s = 4 * p * (1 - p) at hg
  have hz : 0 < z := by linarith [hg.1.2, hg.2.1]
  have hzSq : z ^ 2 = 1 - s := Real.sq_sqrt (by linarith [hs1.2])
  have hzLo : (15 / 16 : ℝ) ≤ z := by nlinarith [hs.2]
  have hpLo : s / 4 ≤ p := by nlinarith [sq_nonneg p]
  have hpHi : p ≤ (8 / 31 : ℝ) * s := by nlinarith [hg.1.1, hg.2.1, hg.2.2]
  have hden : 0 < 1 - 2 * p := by linarith [hg.1.2]
  have hlog := Real.log_le_sub_one_of_pos (by linarith [hg.1.2] : 0 < 1 - p)
  have hterm := mul_le_mul_of_nonneg_left hlog (sq_nonneg (1 - p))
  have hP : 0 ≤ p * (1 - p) := mul_nonneg hg.1.1.le (by linarith [hg.1.2])
  have hbase : p ^ 2 * Real.log p / (1 - 2 * p) ≤ lrLowerFaceOmegaR0 s 0 := by
    rw [omega_zero_p_formula hs1]
    change _ ≤ (p ^ 2 * Real.log p - (1 - p) ^ 2 * Real.log (1 - p)) /
      (1 - 2 * p) - p * (1 - p)
    rw [le_sub_iff_add_le, le_div_iff₀ hden, add_mul, div_mul_cancel₀ _ hden.ne']
    have hgood := mul_nonneg (sq_nonneg p) (by linarith [hg.1.2] : 0 ≤ 1 - p)
    nlinarith
  have hratio : p ^ 2 / (1 - 2 * p) ≤ s ^ 2 / 14 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    have hs0 := hs.1.le
    have hsquare : p ^ 2 ≤ (64 / 961 : ℝ) * s ^ 2 := by nlinarith [hg.1.1]
    have hscaled := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hzLo)
    nlinarith [hg.2.1]
  have harg : 1 / p ≤ 4 / s := by
    rw [div_le_div_iff₀ hg.1.1 hs.1]
    linarith
  have hlogOrder := Real.log_le_log (div_pos (by norm_num) hg.1.1) harg
  have hlog0 : 0 ≤ Real.log (4 / s) := Real.log_nonneg (by
    rw [one_le_div₀ hs.1]
    linarith [hs.2])
  have hmul := mul_le_mul_of_nonneg_left hlogOrder
    (div_nonneg (sq_nonneg p) hden.le)
  have hmul2 := mul_le_mul_of_nonneg_right hratio hlog0
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hg.1.1.ne'] at hmul
  norm_num only [Real.log_one, zero_sub] at hmul
  have hid : p ^ 2 * Real.log p / (1 - 2 * p) =
      -(p ^ 2 / (1 - 2 * p) * -Real.log p) := by ring
  rw [hid] at hbase
  linarith

lemma pwR0_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    (1 + 1 / lrCertificateV p) * lrLowerFaceOmegaR0 p.s 0 ≤
      lrLowerFacePWR0 p.s p.k p.chi (lrCertificateV p) := by
  have hv := lrCertificateV_mem_Ioo hi
  have hy : lrCertificateY0 p ∈ Ico (0 : ℝ) 1 := by
    refine ⟨mul_nonneg hi.2.2.1.le hi.2.1.1.le, ?_⟩
    exact (mul_le_of_le_one_left hi.2.1.1.le hi.2.2.2.le).trans_lt hi.2.1.2
  have hmono := lrLowerFaceOmegaR0_monotoneOn_Ico hi.1
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 := hmono hzero hy hy.1
  have h2 := hmono hzero ⟨hi.2.1.1.le, hi.2.1.2⟩ hi.2.1.1.le
  have h2d := div_le_div_of_nonneg_right h2 hv.1.le
  unfold lrLowerFacePWR0
  change _ ≤ lrLowerFaceOmegaR0 p.s (lrCertificateY0 p) +
    lrLowerFaceOmegaR0 p.s (lrCertificateE p) / lrCertificateV p
  have hid : (1 + 1 / lrCertificateV p) * lrLowerFaceOmegaR0 p.s 0 =
      lrLowerFaceOmegaR0 p.s 0 + lrLowerFaceOmegaR0 p.s 0 / lrCertificateV p := by ring
  rw [hid]
  exact add_le_add h1 h2d

lemma channel_r0_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    (5 / 3 : ℝ) * lrCertificateBFlow p * lrLowerFaceOmegaR0 p.s 0 ≤
      lrSmallSBridgeChannelReserve (lrCertificateD p) (lrCertificateBFlow p)
        (lrCertificateV p) (lrCertificateX p) (lrLowerFaceOmegaR0 p.s 0)
        (lrSmallSBridgeR0G p) (lrLowerFacePWR0 p.s p.k p.chi (lrCertificateV p)) := by
  let v := lrCertificateV p
  let x := lrCertificateX p
  let W := lrLowerFaceOmegaR0 p.s 0
  let B := lrCertificateBFlow p
  let D := lrCertificateD p
  let P := lrLowerFacePWR0 p.s p.k p.chi v
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hvLo : (3 / 4 : ℝ) ≤ v := v_lower hi hs hk
  have hxLo : (17 / 20 : ℝ) ≤ x := by
    have ht := hr.1.2.1
    change p.chi * lrCertificateE p ≤ 3 / 20 at ht
    dsimp [x, lrCertificateX]
    linarith
  have hW : W ≤ 0 := lrLowerFaceOmegaR0_zero_nonpos hi.1
  have hB : 0 ≤ B := (lrCertificateBFlow_pos hi).le
  have hD : 0 ≤ D := (lrDeterminantD1_nonnegative hi).trans (lrDeterminantD1_le_D hi)
  have hp : (1 + 1 / v) * W ≤ P := pwR0_lower hi
  have hg : 0 ≤ lrSmallSBridgeR0G p := by
    have hy : lrCertificateY0 p ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hi.2.2.1.le hi.2.1.1.le,
        (mul_le_of_le_one_left hi.2.1.1.le hi.2.2.2.le).trans_lt hi.2.1.2⟩
    exact add_nonneg (lrLowerFaceR0_nonneg_closed hy)
      (div_nonneg (lrLowerFaceR0_nonneg hi.2.1) hv.1.le)
  have hden : 0 < v * (1 + v) := mul_pos hv.1 (by linarith)
  have hXcoeff : 1 + 1 / v - 4 / (1 + v) - 2 * (v / (1 + v)) ≤ 0 := by
    have hid : 1 + 1 / v - 4 / (1 + v) - 2 * (v / (1 + v)) =
        (1 - 2 * v - v ^ 2) / (v * (1 + v)) := by field_simp; ring
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hden.le
  have hYcoeff : 1 + 1 / v - 2 * (v / (1 + v)) * x ≤ (5 / 3 : ℝ) := by
    have hinv : 1 / v ≤ (4 / 3 : ℝ) := by rw [div_le_iff₀ hv.1]; linarith
    have hM : (3 / 7 : ℝ) ≤ v / (1 + v) := by
      rw [le_div_iff₀ (by linarith : 0 < 1 + v)]
      linarith
    have hm0 : 0 ≤ v / (1 + v) := div_nonneg hv.1.le (by linarith)
    have hprod := mul_le_mul hM hxLo (by norm_num : (0 : ℝ) ≤ 17 / 20) hm0
    linarith
  have hXmul := mul_nonneg_of_nonpos_of_nonpos hXcoeff hW
  have hYmul := mul_le_mul_of_nonpos_right hYcoeff hW
  have hX : 0 ≤ lrSmallSBridgeChannelX v W (lrSmallSBridgeR0G p) P := by
    unfold lrSmallSBridgeChannelX
    rw [show 4 * W / (1 + v) = (4 / (1 + v)) * W by ring]
    nlinarith only [hp, hg, hXmul]
  have hY : (5 / 3 : ℝ) * W ≤ lrSmallSBridgeChannelY v x W P := by
    unfold lrSmallSBridgeChannelY
    nlinarith
  have h1 := mul_nonneg hD hX
  have h2 := mul_le_mul_of_nonneg_left hY hB
  unfold lrSmallSBridgeChannelReserve
  change 5 / 3 * B * W ≤ _
  nlinarith

end CourtadeKumar.LRAnalyticMidpoint
