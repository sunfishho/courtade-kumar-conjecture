import InformationTheory.CourtadeKumar.TopCapPositivity

/-! Closure of the corrected balanced-root reserve using the certified TOP
cap argument. -/

open Set

namespace CourtadeKumar

lemma topCapR_balancedCap {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    topCapR (balancedCap rho r) (r ^ 2) = rho ^ 2 := by
  have hden := (balancedCapDen_pos hrho hr).ne'
  have hden' : 1 - rho ^ 2 * r ^ 2 ≠ 0 := by
    simpa [balancedCapDen] using hden
  have hrden : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hnum : 1 - balancedCap rho r ^ 2 =
      rho ^ 2 * (1 - r ^ 2) / balancedCapDen rho r := by
    rw [balancedCap_sq hrho hr]
    unfold topS topR balancedCapDen
    field_simp [hden']
    ring
  have hcapden : 1 - balancedCap rho r ^ 2 * r ^ 2 =
      (1 - r ^ 2) / balancedCapDen rho r := by
    simpa [mul_pow] using one_sub_balancedCap_mul_ray_sq hrho hr
  unfold topCapR
  rw [hnum, hcapden]
  field_simp [hden, hrden]

theorem topChannelH_balancedCap_nonneg {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topChannelH (rho ^ 2) (balancedCap rho r) (r ^ 2) := by
  have hcap := balancedCap_mem_Ioo_strict hrho hr
  have hq : r ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  have h := topCapH_nonneg hcap hq
  unfold topCapH at h
  rw [topCapR_balancedCap hrho hr] at h
  exact h

/-- Positivity of the normalized corrected reserve at every interior
balanced entropy root. -/
theorem topChannelH_nonneg_at_balancedRoot
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hroot : balancedResidual rho c r = 0) :
    0 ≤ topChannelH (rho ^ 2) c (r ^ 2) := by
  exact (topChannelH_balancedCap_nonneg hrho hr).trans
    (topChannelH_balancedRoot_ge_cap hrho hr hc hroot)

/-- The corrected TOP reserve is nonnegative at every interior balanced
root. -/
theorem topReserve_nonneg_at_balancedRoot
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hroot : balancedResidual rho c r = 0) :
    0 ≤ topReserve rho c r := by
  rw [topReserve_eq_scale_mul_topChannelH_sqCoordinates hrho hr hc.1.ne']
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (topS_pos hrho).le hc.1.le) (sq_nonneg r))
    (topChannelH_nonneg_at_balancedRoot hrho hr hc hroot)

/-- Final scalar closure of the corrected balanced reserve. -/
theorem balancedReserve_nonneg_at_root
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hroot : balancedResidual rho c r = 0) :
    0 ≤ balancedReserve rho c r := by
  rw [← topReserve_eq_balancedReserve rho c r hroot]
  exact topReserve_nonneg_at_balancedRoot hrho hr hc hroot

end CourtadeKumar
