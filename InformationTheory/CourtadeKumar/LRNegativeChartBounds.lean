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

/-! The manuscript's termwise endpoint-kernel estimate is false: at
`R = 1/2`, its fourth coefficient is `11/896`, exceeding the asserted `8/896`.
Only the aggregate bound `4*W ≤ 1-R` is needed.  The following existing
endpoint-coordinate argument proves that bound directly, without the false
coefficient estimate. -/

lemma lrScalarEndpointUpper_le_quarter_aux
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    lrScalarEndpointUpper z ≤ z * (1 + 2 * z) / (1 + z) ^ 2 := by
  have hz1 : 0 < 1 + z := by linarith [hz.1]
  have hz2 : 0 < 2 + z := by linarith [hz.1]
  unfold lrScalarEndpointUpper
  rw [div_le_div_iff₀
    (mul_pos (mul_pos (by norm_num) (by linarith : 0 < z + 1))
      (by linarith : 0 < z + 2))
    (sq_pos_of_pos hz1)]
  have hfac : 0 ≤ z ^ 2 * (z + 1) * (6 - z - z ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg z) (by linarith [hz.1]))
      (by nlinarith [hz.1, hz.2])
  ring_nf at hfac ⊢
  nlinarith

lemma two_mul_lrScalarLogRatio_le_neg_log
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    2 * lrScalarLogRatio z ≤ -Real.log z := by
  have h := lrScalarLogLower_le_neg_log hz
  have hr := (lrScalarLogRatio_mem_Ioo hz).1.le
  unfold lrScalarLogLower at h
  dsimp only at h
  nlinarith [pow_nonneg hr 3]

lemma lrWKernel_one_eq_endpoint_coordinates
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrWKernel R 1 =
      Real.log (1 + lrBEndpointZ R) -
        (lrBEndpointZ R) ^ 2 * (-Real.log (lrBEndpointZ R)) /
          (1 - (lrBEndpointZ R) ^ 2) := by
  have hz := lrBEndpointZ_mem_Ioo hR
  have hzden : 1 - (lrBEndpointZ R) ^ 2 ≠ 0 := by
    nlinarith [hz.1, hz.2]
  have hsqrt := lrB_sqrt_mem_Ioo hR
  rw [show lrWKernel R 1 = lrBDelta R -
      (1 - R) * Real.artanh (Real.sqrt R) / (2 * Real.sqrt R) by
    unfold lrWKernel lrBDelta
    simp only [topPhi_one, mul_one]
    ring]
  rw [lrBDelta_eq_endpoint_coordinates hR,
    lrBEndpointN_eq_coordinates hR]
  have hzplus : 1 + lrBEndpointZ R ≠ 0 := by linarith [hz.1]
  field_simp [hzden, hzplus]
  ring

/-- The endpoint kernel bound needed by the negative chart. -/
theorem four_mul_lrWKernel_one_le_one_sub
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    4 * lrWKernel R 1 ≤ 1 - R := by
  let z := lrBEndpointZ R
  have hz : z ∈ Ioo (0 : ℝ) 1 := lrBEndpointZ_mem_Ioo hR
  have hzClosed : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2.le⟩
  have hz1 : 0 < 1 + z := by linarith [hz.1]
  have hzden : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hlog := log_one_add_le_lrScalarEndpointUpper hzClosed
  have hupper := lrScalarEndpointUpper_le_quarter_aux hzClosed
  have hell := two_mul_lrScalarLogRatio_le_neg_log hz
  have hratio : lrScalarLogRatio z = (1 - z) / (1 + z) := rfl
  have hterm : 2 * z ^ 2 / (1 + z) ^ 2 ≤
      z ^ 2 * (-Real.log z) / (1 - z ^ 2) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hz1) hzden]
    rw [hratio] at hell
    have hscaled := mul_le_mul_of_nonneg_left hell
      (mul_nonneg (sq_nonneg z) (sq_nonneg (1 + z)))
    convert hscaled using 1 <;> field_simp [hz1.ne'] <;> ring
  have hW : lrWKernel R 1 ≤ z / (1 + z) ^ 2 := by
    rw [lrWKernel_one_eq_endpoint_coordinates hR]
    change Real.log (1 + z) - z ^ 2 * (-Real.log z) / (1 - z ^ 2) ≤ _
    calc
      Real.log (1 + z) - z ^ 2 * (-Real.log z) / (1 - z ^ 2) ≤
          lrScalarEndpointUpper z - 2 * z ^ 2 / (1 + z) ^ 2 :=
        sub_le_sub hlog hterm
      _ ≤ z * (1 + 2 * z) / (1 + z) ^ 2 -
          2 * z ^ 2 / (1 + z) ^ 2 := sub_le_sub_right hupper _
      _ = z / (1 + z) ^ 2 := by
        field_simp [hz1.ne']
        ring
  have hsCoord : 1 - R = 4 * z / (1 + z) ^ 2 := by
    have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
    have hplus : 1 + Real.sqrt R ≠ 0 := by positivity
    unfold z lrBEndpointZ lrScalarLogRatio
    field_simp [hplus]
    nlinarith [hsqrtSq]
  rw [hsCoord]
  have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ (4 : ℝ) by norm_num)
  convert hh using 1 <;> field_simp [hz1.ne'] <;> ring

end CourtadeKumar
