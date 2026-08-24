import InformationTheory.CourtadeKumar.BalancedRootCap

/-! Differential reduction of the cap residual to the auxiliary function `F`. -/

open Set

namespace CourtadeKumar

noncomputable def topL0 (r : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (1 - r ^ 2)

lemma topJ_add_mul_artanh {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    topJ r + r * Real.artanh r = Real.log 2 + topL0 r := by
  have hm : 0 < 1 - r := by linarith [hr.2]
  have hp : 0 < 1 + r := by linarith [hr.1]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [topJ_eq_binEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [Real.artanh_eq_half_log ⟨hr.1.le, hr.2.le⟩]
  rw [Real.negMulLog_eq_neg]
  change
    (-(((1 - r) / 2) * Real.log ((1 - r) / 2))) +
        (-((1 - ((1 - r) / 2)) * Real.log (1 - ((1 - r) / 2)))) +
        r * (1 / 2 * Real.log ((1 + r) / (1 - r))) =
      Real.log 2 + topL0 r
  rw [show 1 - (1 - r) / 2 = (1 + r) / 2 by ring]
  rw [Real.log_div hm.ne' htwo, Real.log_div hp.ne' htwo,
    Real.log_div hp.ne' hm.ne']
  have hprod : (1 - r) * (1 + r) = 1 - r ^ 2 := by ring
  calc
    _ = Real.log 2 - (1 / 2 : ℝ) *
        (Real.log (1 - r) + Real.log (1 + r)) := by ring
    _ = Real.log 2 - (1 / 2 : ℝ) * Real.log ((1 - r) * (1 + r)) := by
      rw [Real.log_mul hm.ne' hp.ne']
    _ = Real.log 2 + topL0 r := by
      rw [hprod]
      unfold topL0
      ring

theorem hasDerivAt_balancedCap {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (balancedCap rho)
      (rho ^ 2 * balancedCap rho r * r / balancedCapDen rho r) r := by
  have hdenpos := balancedCapDen_pos hrho hr
  have hdenne := hdenpos.ne'
  have hspos := topS_pos hrho
  have hdenDeriv : HasDerivAt (balancedCapDen rho)
      (-2 * rho ^ 2 * r) r := by
    unfold balancedCapDen
    convert (hasDerivAt_const r 1).sub
      ((hasDerivAt_const r (rho ^ 2)).mul ((hasDerivAt_id r).pow 2)) using 1
    simp [id_eq]
    ring_nf
  have hratio := (hasDerivAt_const r (topS rho)).div hdenDeriv hdenne
  have hratio_pos : 0 < topS rho / balancedCapDen rho r := div_pos hspos hdenpos
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hratio_pos)).comp r hratio
  unfold balancedCap
  convert hsqrt using 1
  rw [show Real.sqrt (topS rho / balancedCapDen rho r) = balancedCap rho r by rfl]
  have hcapsq := balancedCap_sq hrho hr
  have hcapCleared : balancedCap rho r ^ 2 * balancedCapDen rho r = topS rho := by
    rw [hcapsq]
    exact div_mul_cancel₀ _ hdenne
  field_simp [hdenne, ne_of_gt (balancedCap_pos hrho hr)]
  linear_combination (2 * rho ^ 2 * r) * hcapCleared

theorem hasDerivAt_balancedCap_mul_ray {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z ↦ balancedCap rho z * z)
      (balancedCap rho r / balancedCapDen rho r) r := by
  have h := (hasDerivAt_balancedCap hrho hr).mul (hasDerivAt_id r)
  have hdenne := (balancedCapDen_pos hrho hr).ne'
  convert h using 1
  simp only [id_eq]
  field_simp [hdenne]
  unfold balancedCapDen
  ring_nf

noncomputable def balancedCapAuxF (rho r : ℝ) : ℝ :=
  Real.artanh r - topS rho * Real.artanh (balancedCap rho r * r) -
    rho ^ 2 * r * (Real.log 2 + topL0 r) -
      2 * topEll rho * (balancedCap rho r * r)

noncomputable def balancedCapResidual (rho r : ℝ) : ℝ :=
  balancedResidual rho (balancedCap rho r) r

/-- Along the explicit cap, the balanced residual decreases at a rate
controlled exactly by the auxiliary function `F`. -/
theorem hasDerivAt_balancedCapResidual {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (balancedCapResidual rho)
      (-(balancedCap rho r / balancedCapDen rho r) * balancedCapAuxF rho r) r := by
  have hc := hasDerivAt_balancedCap hrho hr
  have hrid := hasDerivAt_id r
  have hw := hasDerivAt_balancedCap_mul_ray hrho hr
  have hjr := hasDerivAt_topJ (show r ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hr.1], hr.2⟩)
  have hwmem := balancedCap_mul_ray_mem_Ioo hrho hr
  have hjw := hasDerivAt_topJ
    (show balancedCap rho r * r ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hwmem.1], hwmem.2⟩)
  have hfirst := hc.mul hjr
  have hjwcomp := hjw.comp_of_eq r hw rfl
  have hmiddle := hjwcomp.const_mul (topS rho)
  have hwSq := hw.pow 2
  have hlast := ((hasDerivAt_const r 1).sub hwSq).const_mul (topEll rho)
  have htotal := (hfirst.sub hmiddle).sub hlast
  unfold balancedCapResidual balancedResidual
  convert htotal using 1
  · funext z
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
    ring_nf
  · unfold balancedCapAuxF
    rw [← topJ_add_mul_artanh
      (show r ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hr.1], hr.2⟩)]
    field_simp [(balancedCapDen_pos hrho hr).ne']
    unfold balancedCapDen
    ring_nf

end CourtadeKumar
