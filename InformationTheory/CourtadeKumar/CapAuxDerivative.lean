import InformationTheory.CourtadeKumar.CapResidualDerivative

/-! Exact first derivative of the balanced-cap auxiliary function. -/

open Set

namespace CourtadeKumar

noncomputable def balancedCapAuxFDeriv (rho r : ℝ) : ℝ :=
  rho ^ 2 * (balancedCap rho r + 1 / (1 + balancedCap rho r) -
    Real.log 2 - topL0 r) -
      2 * topEll rho * balancedCap rho r / balancedCapDen rho r

theorem hasDerivAt_topL0 {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt topL0 (r / (1 - r ^ 2)) r := by
  have harg : HasDerivAt (fun z : ℝ ↦ 1 - z ^ 2) (-2 * r) r := by
    convert (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2) using 1
    simp [id_eq]
  have hne : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hlog := (Real.hasDerivAt_log hne).comp r harg
  unfold topL0
  convert hlog.const_mul (-(1 / 2 : ℝ)) using 1
  ring_nf

/-- Exact first derivative of the cap auxiliary function. -/
theorem hasDerivAt_balancedCapAuxF {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (balancedCapAuxF rho) (balancedCapAuxFDeriv rho r) r := by
  have hrfull : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
  have hw := hasDerivAt_balancedCap_mul_ray hrho hr
  have hwmem := balancedCap_mul_ray_mem_Ioo hrho hr
  have hwfull : balancedCap rho r * r ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hwmem.1], hwmem.2⟩
  have hfirst := hasDerivAt_artanh hrfull
  have hsecondInner := (hasDerivAt_artanh hwfull).comp_of_eq r hw rfl
  have hsecond := hsecondInner.const_mul (topS rho)
  have hL0 := hasDerivAt_topL0 hrfull
  have hsum := (hasDerivAt_const r (Real.log 2)).add hL0
  have hproduct := (hasDerivAt_id r).mul hsum |>.const_mul (rho ^ 2)
  have hlast := hw.const_mul (2 * topEll rho)
  have htotal := ((hfirst.sub hsecond).sub hproduct).sub hlast
  unfold balancedCapAuxF balancedCapAuxFDeriv
  convert htotal using 1
  · funext z
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply, id_eq]
    ring_nf
  · have hden := balancedCapDen_pos hrho hr
    have hone : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have hwidentity := one_sub_balancedCap_mul_ray_sq hrho hr
    have hcapsq := balancedCap_sq hrho hr
    have hcapPos := balancedCap_pos hrho hr
    have hcapPlus : 1 + balancedCap rho r ≠ 0 := by positivity
    simp only [Pi.add_apply, id_eq, one_mul, zero_add]
    rw [hwidentity]
    have hcapCleared : balancedCap rho r ^ 2 * balancedCapDen rho r = topS rho := by
      rw [hcapsq]
      exact div_mul_cancel₀ _ hden.ne'
    have hkey :
        (1 + balancedCap rho r) *
            (1 - topS rho * balancedCap rho r - rho ^ 2 * r ^ 2) =
          rho ^ 2 * (1 - r ^ 2) *
            (balancedCap rho r * (1 + balancedCap rho r) + 1) := by
      unfold topS topR
      unfold topS topR balancedCapDen at hcapCleared
      linear_combination (-1) * hcapCleared
    have hcore :
        1 / (1 - r ^ 2) -
              topS rho * (1 / ((1 - r ^ 2) / balancedCapDen rho r) *
                (balancedCap rho r / balancedCapDen rho r)) -
              rho ^ 2 * r * (r / (1 - r ^ 2)) =
            rho ^ 2 *
              (balancedCap rho r + 1 / (1 + balancedCap rho r)) := by
      have hcancel :
          1 / ((1 - r ^ 2) / balancedCapDen rho r) *
              (balancedCap rho r / balancedCapDen rho r) =
            balancedCap rho r / (1 - r ^ 2) := by
        field_simp [hden.ne', hone.ne']
      rw [hcancel]
      field_simp [hone.ne', hcapPlus]
      linear_combination hkey
    change
      rho ^ 2 * (balancedCap rho r + 1 / (1 + balancedCap rho r) -
          Real.log 2 - topL0 r) -
          2 * topEll rho * balancedCap rho r / balancedCapDen rho r =
        1 / (1 - r ^ 2) -
          topS rho * (1 / ((1 - r ^ 2) / balancedCapDen rho r) *
            (balancedCap rho r / balancedCapDen rho r)) -
          rho ^ 2 * ((Real.log 2 + topL0 r) + r * (r / (1 - r ^ 2))) -
          2 * topEll rho * (balancedCap rho r / balancedCapDen rho r)
    calc
      _ = rho ^ 2 *
              (balancedCap rho r + 1 / (1 + balancedCap rho r)) -
            rho ^ 2 * (Real.log 2 + topL0 r) -
            2 * topEll rho * (balancedCap rho r / balancedCapDen rho r) := by ring
      _ = (1 / (1 - r ^ 2) -
              topS rho * (1 / ((1 - r ^ 2) / balancedCapDen rho r) *
                (balancedCap rho r / balancedCapDen rho r)) -
              rho ^ 2 * r * (r / (1 - r ^ 2))) -
            rho ^ 2 * (Real.log 2 + topL0 r) -
            2 * topEll rho * (balancedCap rho r / balancedCapDen rho r) := by rw [← hcore]
      _ = _ := by ring

end CourtadeKumar
