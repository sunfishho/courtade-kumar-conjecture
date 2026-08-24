import InformationTheory.CourtadeKumar.TopMonotonicity

/-! The interior derivative of `Real.artanh`, currently absent from Mathlib's API. -/

open Set Filter

namespace CourtadeKumar

theorem hasDerivAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hnum : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x :=
    (hasDerivAt_id x).const_add 1
  have hden : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x :=
    (hasDerivAt_id x).const_sub 1
  have hden_ne : 1 - x ≠ 0 := by linarith [hx.2]
  have hquot := hnum.div hden hden_ne
  have hquot_ne : (1 + x) / (1 - x) ≠ 0 := by
    apply div_ne_zero
    · linarith [hx.1]
    · exact hden_ne
  have hlog := hquot.log hquot_ne
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  simp only [Pi.div_apply] at hhalf
  have hplus_ne : 1 + x ≠ 0 := by linarith [hx.1]
  have hsq_ne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hg : HasDerivAt
      (fun y : ℝ ↦ (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)))
      (1 / (1 - x ^ 2)) x := by
    convert hhalf using 1
    field_simp [hden_ne, hplus_ne, hsq_ne]
    ring
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩

end CourtadeKumar
