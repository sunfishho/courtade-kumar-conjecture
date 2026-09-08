import InformationTheory.CourtadeKumar.LRCompactVSameYLambda
import InformationTheory.CourtadeKumar.LRCompactVLambdaPositiveGroupedReserve

/-! An analytic endpoint reduction for compact V. The same-y multiplier
budget itself implies the formerly separate slope condition. Thus one
endpoint logarithm comparison supplies the budget on a whole rectangle. -/
open Set
namespace CourtadeKumar.LRAnalyticCompact

lemma ratio_slope_numerator {R v y : ℝ}
    (hR : R ∈ Ico (0 : ℝ) 1) (hv : 0 < v) (hy : y ∈ Ico (0 : ℝ) 1) :
    R * (1 - y) * lrCompactVDFullX R y ≤
      (1 - R) * lrCompactVBFullX R v y := by
  have hRy : R * y < 1 :=
    (show R * y ≤ y by simpa using mul_le_mul_of_nonneg_right hR.2.le hy.1).trans_lt hy.2
  have h1y : 0 < 1 - y := sub_pos.mpr hy.2
  have h1Ry : 0 < 1 - R * y := sub_pos.mpr hRy
  have hlog := Real.log_le_sub_one_of_pos (div_pos h1Ry h1y)
  rw [Real.log_div h1Ry.ne' h1y.ne'] at hlog
  have hratio : (1 - R * y) / (1 - y) - 1 = (1 - R) * y / (1 - y) := by
    field_simp [h1y.ne']
    ring
  rw [hratio] at hlog
  have hD : lrCompactVDFullX R y ≤ (1 - R) * y / (2 * (1 - y)) := by
    unfold lrCompactVDFullX
    calc
      (1 / 2 : ℝ) * (Real.log (1 - R * y) - Real.log (1 - y)) ≤
          (1 / 2 : ℝ) * ((1 - R) * y / (1 - y)) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = (1 - R) * y / (2 * (1 - y)) := by field_simp [h1y.ne'] <;> ring
  have hlog2 := Real.log_le_sub_one_of_pos h1Ry
  have hbeta : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hB : R * y / 2 ≤ lrCompactVBFullX R v y := by
    unfold lrCompactVBFullX
    linarith
  have hmulD := mul_le_mul_of_nonneg_left hD
    (mul_nonneg hR.1 h1y.le)
  have hid : R * (1 - y) * ((1 - R) * y / (2 * (1 - y))) =
      (1 - R) * (R * y / 2) := by
    field_simp [h1y.ne']
  rw [hid] at hmulD
  exact hmulD.trans (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hR.2.le))

lemma b_positive {R v y : ℝ}
    (hR : R ∈ Ico (0 : ℝ) 1) (hv : 0 < v) (hy : y ∈ Ico (0 : ℝ) 1) :
    0 < lrCompactVBFullX R v y := by
  have hRy : R * y < 1 :=
    (show R * y ≤ y by simpa using mul_le_mul_of_nonneg_right hR.2.le hy.1).trans_lt hy.2
  have hlog : Real.log (1 - R * y) ≤ 0 :=
    Real.log_nonpos (by linarith) (by nlinarith [mul_nonneg hR.1 hy.1])
  have hbeta := Real.log_pos (show 1 < 1 + v by linarith)
  unfold lrCompactVBFullX
  linarith

/-- No additional slope certificate is needed after a valid endpoint budget. -/
theorem slope_of_endpoint_budget {lambda R v y : ℝ}
    (hR : R ∈ Ico (0 : ℝ) 1) (hv : 0 < v) (hy : y ∈ Ico (0 : ℝ) 1)
    (hbudget : lambda * lrCompactVBFullX R v y ≤ lrCompactVDFullX R y) :
    lambda * R * (1 - y) ≤ 1 - R := by
  have hbase := ratio_slope_numerator hR hv hy
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (mul_nonneg hR.1 (sub_nonneg.mpr hy.2.le))
  have hB := b_positive hR hv hy
  apply (mul_le_mul_iff_of_pos_right hB).mp
  nlinarith

/-- A single same-y endpoint comparison gives the budget on the full region.
This retains the shared y coordinate and removes the separate slope premise. -/
theorem budget_on_rectangle {lambda R RHi v vHi yLo y : ℝ}
    (hlambda : 0 ≤ lambda) (hR : 0 ≤ R) (hRR : R ≤ RHi) (hRHi : RHi < 1)
    (hv : 0 < v) (hvv : v ≤ vHi)
    (hyLo : 0 ≤ yLo) (hyy : yLo ≤ y) (hy : y < 1)
    (hbudget : lambda * lrCompactVBFullX RHi vHi yLo ≤ lrCompactVDFullX RHi yLo) :
    lambda * lrCompactVBFullX R v y ≤ lrCompactVDFullX R y := by
  have hslope := slope_of_endpoint_budget
    ⟨hR.trans hRR, hRHi⟩ (hv.trans_le hvv) ⟨hyLo, hyy.trans_lt hy⟩ hbudget
  have h1 := lrCompactVSameYSlack_mono_y (v := vHi)
    hlambda (hR.trans hRR) hRHi hyLo hyy hy hslope
  have h2 := lrCompactVSameYSlack_anti_v (R := RHi) (y := y) hlambda hv.le hvv
  have h3 := lrCompactVSameYSlack_anti_R (v := v) hlambda hRR hRHi (hyLo.trans hyy) hy
  have h := h1.trans (h2.trans h3)
  unfold lrCompactVSameYSlack at h
  linarith

/-- The existing rational endpoint budget suffices for a checked multiplier;
the previous additional rational slope check can be omitted. -/
theorem checked_lambda_mul_flowB_le_flowD
    (logTerms halfLogTerms dTerms : ℕ) (lambda : ℚ)
    {box : CertificateBox} {point : CertificatePoint}
    {logOnePlusVHi : RationalEnclosure.LogRangeCertificate}
    (hvalid : LRCompactVDirectDValid box)
    (hpoint : box.Contains point) (hi : LRCompactVInterior point)
    (hlambda : (0 : ℚ) ≤ lambda)
    (hlogcheck : logOnePlusVHi.check (1 + box.kHi) = true)
    (hbudget : lambda *
        (lrCompactVSameYBEndpointEnclosure logTerms halfLogTerms box logOnePlusVHi).upper ≤
        (lrCompactVDirectDEnclosure dTerms box).nonnegativeLower) :
    (lambda : ℝ) * lrFlowB point.s point.k (Real.sqrt point.chi) ≤
      lrFlowD point.s point.k (Real.sqrt point.chi) := by
  have hRHi0 : (0 : ℝ) ≤ box.sHi := by
    exact_mod_cast hvalid.1.1.trans hvalid.1.2.1
  have hRHi1 : (box.sHi : ℝ) < 1 := by exact_mod_cast hvalid.2.1
  have hvHi : (0 : ℝ) < box.kHi := hi.2.1.1.trans_le hpoint.2.2.2.1
  have hyLo0 : (0 : ℝ) ≤ lrCompactVDirectDYLoQ box := by
    rw [cast_lrCompactVDirectDYLoQ]
    exact mul_nonneg (sq_nonneg _) (by exact_mod_cast hvalid.1.2.2.2.2.2.2.1)
  have hyLo1 : (lrCompactVDirectDYLoQ box : ℝ) < 1 := by exact_mod_cast hvalid.2.2
  have harg : 1 - (lrCompactVDirectDYLoQ box : ℝ) ≤
      1 - (box.sHi : ℝ) * (lrCompactVDirectDYLoQ box : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hRHi1.le hyLo0]
  have hlog := Real.log_le_log (by linarith : 0 < 1 - (lrCompactVDirectDYLoQ box : ℝ)) harg
  have hD0 : 0 ≤ lrCompactVDFullX (box.sHi : ℝ) (lrCompactVDirectDYLoQ box : ℝ) := by
    unfold lrCompactVDFullX
    linarith
  have hB := lrCompactVSameYBEndpointEnclosure_sound logTerms halfLogTerms hvalid hlogcheck
  have hD := lrCompactVDirectDEnclosure_contains_corner dTerms hvalid
  have hendpoint := cast_lrCompactVCheckedLambda_mul_le hlambda hB.2 hbudget hD.1 hD0
  have hslope := slope_of_endpoint_budget ⟨hRHi0, hRHi1⟩ hvHi ⟨hyLo0, hyLo1⟩ hendpoint
  apply lrCompactVSameYCheckedLambda_mul_flowB_le_flowD
    logTerms halfLogTerms dTerms lambda hvalid hpoint hi hlambda hlogcheck hbudget
  exact_mod_cast hslope

end CourtadeKumar.LRAnalyticCompact
