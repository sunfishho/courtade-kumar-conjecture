import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantElementary
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointEndpointBudget

/-! Entropy and slope bounds for the complete finite determinant strip. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

lemma s_log_upper {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    s * Real.log (4 / s) ≤ 1 / 2 := by
  have heq : Real.log (4 / (1 / 8 : ℝ)) = 5 * Real.log 2 := by
    rw [show (4 / (1 / 8 : ℝ)) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hEnd : 1 ≤ Real.log (4 / (1 / 8 : ℝ)) := by
    rw [heq]; nlinarith [Real.log_two_gt_d9]
  have h := mul_log_four_div_le_endpoint hs.1 (by norm_num : (0 : ℝ) < 1 / 8)
    (hs.2.trans (by norm_num)) hEnd
  rw [heq] at h
  nlinarith [Real.log_two_lt_d9]

lemma r0_upper {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 10)) :
    lrLowerFaceR0 s ≤ s ^ 2 / 15 * Real.log (4 / s) := by
  have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  let p := lrLowerFaceP s
  let z := Real.sqrt (1 - s)
  have hg := lrLowerFaceP_geometry hs1
  change p ∈ Ioo (0 : ℝ) (1 / 2) ∧ 1 - 2 * p = z ∧ s = 4 * p * (1 - p) at hg
  have hzSq : z ^ 2 = 1 - s := Real.sq_sqrt (by linarith [hs1.2])
  have hzLo : (15 / 16 : ℝ) ≤ z := by
    have hz : 0 < z := by linarith [hg.1.2, hg.2.1]
    nlinarith [hs.2]
  have hpLo : s / 4 ≤ p := by nlinarith [sq_nonneg p]
  have hpHi : p ≤ (8 / 31 : ℝ) * s := by nlinarith [hg.1.1, hg.2.1, hg.2.2]
  have hp1 : 0 < 1 - p := by linarith [hg.1.2]
  have hl := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 1) hp1)
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hp1.ne'] at hl
  norm_num only [Real.log_one, zero_sub] at hl
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (1 - p))
  have hid : (1 - p) ^ 2 * (1 / (1 - p) - 1) = p * (1 - p) := by
    field_simp [hp1.ne']; ring
  rw [hid] at hm
  have hbase : lrLowerFaceR0 s ≤ p ^ 2 * Real.log (1 / p) := by
    rw [lrLowerFaceR0_eq_pFormula hs1]
    unfold lrLowerFaceR0PFormula
    simp only [Real.negMulLog_eq_neg]
    change p * -(p * Real.log p) + (1 - p) * -((1 - p) * Real.log (1 - p)) -
      p * (1 - p) ≤ p ^ 2 * Real.log (1 / p)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hg.1.1.ne']
    norm_num only [Real.log_one, zero_sub]
    nlinarith
  have harg : 1 / p ≤ 4 / s := by
    rw [div_le_div_iff₀ hg.1.1 hs.1]; linarith
  have hlog := Real.log_le_log (div_pos (by norm_num) hg.1.1) harg
  have hC : 0 ≤ Real.log (4 / s) := by
    linarith [LRAnalyticMidpoint.log_four_div_ge hs]
  have hsq : p ^ 2 ≤ s ^ 2 / 15 := by
    have hsq' : p ^ 2 ≤ (64 / 961 : ℝ) * s ^ 2 := by nlinarith [hg.1.1]
    nlinarith [sq_nonneg s]
  exact hbase.trans ((mul_le_mul_of_nonneg_left hlog (sq_nonneg p)).trans
    (mul_le_mul_of_nonneg_right hsq hC))

lemma half_base_upper {v : ℝ} (hv : v ∈ Icc (3 / 4 : ℝ) 1) :
    4 * (1 + v) ^ 2 / v ^ 2 *
      (Real.log 2 + Real.log (1 + v) - Real.log (2 + v)) ≤ 16 / 3 := by
  have hv0 : 0 < v := by linarith [hv.1]
  have h1 : 0 < 1 + v := by linarith
  have h2 : 0 < 2 + v := by linarith
  have h := LRAnalyticMidpoint.log_ratio_trapezoid
    h2 (show 2 + v ≤ 2 * (1 + v) by linarith)
  rw [Real.log_div (mul_pos (by norm_num) h1).ne' h2.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h1.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * (1 + v) ^ 2 / v ^ 2 by positivity)
  have hid : 4 * (1 + v) ^ 2 / v ^ 2 *
      ((2 * (1 + v) - (2 + v)) * (2 * (1 + v) + (2 + v)) /
        (2 * (2 * (1 + v)) * (2 + v))) =
      (1 + v) * (4 + 3 * v) / (v * (2 + v)) := by
    field_simp [hv0.ne', h1.ne', h2.ne']; ring
  rw [hid] at hm
  apply hm.trans
  rw [div_le_iff₀ (mul_pos hv0 h2)]
  nlinarith [hv.1]

lemma hd_upper {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrDeterminantHd p ≤ Real.log (4 / p.s) + 15 / 4 := by
  have hv := lrCertificateV_mem_Ioo hi
  have hb := half_base_upper ⟨LRAnalyticMidpoint.v_lower hi hs hk, hv.2.le⟩
  have hr := r0_upper ⟨hi.1.1, hs⟩
  have hsr := div_le_div_of_nonneg_right hr hi.1.1.le
  have hid : (p.s ^ 2 / 15 * Real.log (4 / p.s)) / p.s =
      p.s * Real.log (4 / p.s) / 15 := by field_simp [hi.1.1.ne'] <;> ring
  rw [hid] at hsr
  have hlog := s_log_upper ⟨hi.1.1, hs⟩
  have heq : lrDeterminantHd p =
      4 * (1 + lrCertificateV p) ^ 2 / (lrCertificateV p) ^ 2 *
        (Real.log 2 + Real.log (1 + lrCertificateV p) - Real.log (2 + lrCertificateV p)) +
      Real.log (4 / p.s) + 1 - 4 * Real.log 2 + 4 * lrLowerFaceR0 p.s / p.s := by
    unfold lrDeterminantHd lrCertificateHalfSlope lrLowerFaceR0 lrLowerFaceQ0
    field_simp [hi.1.1.ne', hv.1.ne']
    ring
  rw [heq, mul_div_assoc 4 (lrLowerFaceR0 p.s) p.s]
  nlinarith [Real.log_two_gt_d9]

end CourtadeKumar.LRAnalyticDeterminant
