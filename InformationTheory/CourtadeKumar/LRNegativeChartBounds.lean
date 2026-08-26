import InformationTheory.CourtadeKumar.LRFlowChartAssembly

/-! Elementary tangent bounds needed by the negative LR flow chart. -/

open Set

namespace CourtadeKumar

noncomputable def lrFlowQ₀ (R v : ℝ) : ℝ :=
  -lrFlowEllDeriv R (lrFlowM v)

noncomputable def lrQ₀LogFactor (v : ℝ) : ℝ :=
  (1 + v) ^ 2 * Real.log (1 + v) / v ^ 2

theorem hasDerivAt_lrQ₀LogFactor
    {v : ℝ} (hv : v ≠ 0) (hv1 : v ≠ -1) :
    HasDerivAt lrQ₀LogFactor
      ((1 + v) / v ^ 3 * (v - 2 * Real.log (1 + v))) v := by
  have hid := hasDerivAt_id v
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 v := by
    simpa using hid.const_add 1
  have hplusne : 1 + v ≠ 0 := by
    intro h
    apply hv1
    linarith
  have hlog := hplus.log hplusne
  have hnum := (hplus.pow 2).mul hlog
  have hden : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * v) v := by
    convert hid.pow 2 using 1
    norm_num
  unfold lrQ₀LogFactor
  convert hnum.div hden (pow_ne_zero 2 hv) using 1
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp [hv]
  ring

lemma v_le_two_mul_log_one_add
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    v ≤ 2 * Real.log (1 + v) := by
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hlog := Real.one_sub_inv_le_log_of_pos hplus
  have hfrac : v / 2 ≤ 1 - (1 + v)⁻¹ := by
    field_simp [hplus.ne']
    nlinarith [hv.1, hv.2]
  linarith

theorem lrQ₀LogFactor_ge_four_log_two
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    4 * Real.log 2 ≤ lrQ₀LogFactor v := by
  have hanti : AntitoneOn lrQ₀LogFactor (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro x hx
      exact (hasDerivAt_lrQ₀LogFactor (by linarith [hv.1, hx.1])
        (by linarith [hv.1, hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrQ₀LogFactor (by linarith [hv.1, hx.1])
        (by linarith [hv.1, hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxClosed : x ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith [hv.1, hx.1], hx.2.le⟩
      have hxpos : 0 < x := by linarith [hv.1, hx.1]
      rw [(hasDerivAt_lrQ₀LogFactor hxpos.ne'
        (by linarith [hxClosed.1])).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (by linarith [hxClosed.1]) (pow_nonneg hxClosed.1 _))
        (sub_nonpos.mpr (v_le_two_mul_log_one_add hxClosed))
  have h := hanti ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ hv.2
  change lrQ₀LogFactor 1 ≤ lrQ₀LogFactor v at h
  have hOne : lrQ₀LogFactor 1 = 4 * Real.log 2 := by
    unfold lrQ₀LogFactor
    norm_num
  rw [hOne] at h
  exact h

lemma lrFlowM_mem_Ioc
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrFlowM v ∈ Ioc (0 : ℝ) (1 / 2) := by
  have hden : 0 < 1 + v := by linarith [hv.1]
  unfold lrFlowM
  constructor
  · exact div_pos hv.1 hden
  · rw [div_le_iff₀ hden]
    linarith [hv.2]

lemma lrFlowQ₀_eq
    {R v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrFlowQ₀ R v =
      (1 - R) * lrQ₀LogFactor v +
        4 * (R * Real.log 2 - topPhi (Real.sqrt R)) := by
  have hden : 0 < 1 + v := by linarith [hv.1]
  have hMne : lrFlowM v ≠ 0 := (lrFlowM_mem_Ioc hv).1.ne'
  have hOneM : 1 - lrFlowM v = 1 / (1 + v) := by
    unfold lrFlowM
    field_simp [hden.ne']
    ring
  unfold lrFlowQ₀ lrFlowEllDeriv lrQ₀LogFactor lrFlowM
  rw [show 1 - v / (1 + v) = 1 / (1 + v) by
      simpa [lrFlowM] using hOneM,
    Real.log_div one_ne_zero hden.ne', Real.log_one]
  field_simp [hv.1.ne', hden.ne', hMne]
  ring

theorem lrFlowQ₀_pos
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 < lrFlowQ₀ R v := by
  unfold lrFlowQ₀
  exact neg_pos.mpr (lrFlowEllDeriv_neg hR (lrFlowM_mem_Ioc hv))

theorem four_delta_le_lrFlowQ₀
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    4 * lrBDelta R ≤ lrFlowQ₀ R v := by
  rw [lrFlowQ₀_eq hv]
  unfold lrBDelta
  have hfactor := lrQ₀LogFactor_ge_four_log_two hv
  have hscaled := mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr hR.2.le)
  nlinarith

end CourtadeKumar
