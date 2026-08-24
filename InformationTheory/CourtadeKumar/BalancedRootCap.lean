import InformationTheory.CourtadeKumar.ChannelCap

/-! Geometry and monotonicity reduction for the corrected balanced-root cap. -/

open Set

namespace CourtadeKumar

noncomputable def balancedCapDen (rho r : ℝ) : ℝ :=
  1 - rho ^ 2 * r ^ 2

noncomputable def balancedCap (rho r : ℝ) : ℝ :=
  Real.sqrt (topS rho / balancedCapDen rho r)

lemma balancedCapDen_pos {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < balancedCapDen rho r := by
  unfold balancedCapDen
  have hrhor : rho * r < 1 := by nlinarith [hrho.1, hrho.2, hr.1, hr.2]
  nlinarith [mul_pos hrho.1 hr.1, sq_nonneg (rho * r)]

lemma topS_pos {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    0 < topS rho := by
  unfold topS topR
  nlinarith [mul_pos (sub_pos.mpr hrho.2) (add_pos_of_pos_of_nonneg hrho.1 zero_le_one)]

lemma topS_le_balancedCapDen {rho r : ℝ}
    (_hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    topS rho ≤ balancedCapDen rho r := by
  unfold topS topR balancedCapDen
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  nlinarith [mul_nonneg (sq_nonneg rho) (sub_nonneg.mpr hr2)]

lemma balancedCap_ratio_pos {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < topS rho / balancedCapDen rho r :=
  div_pos (topS_pos hrho) (balancedCapDen_pos hrho hr)

lemma balancedCap_sq {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho r ^ 2 = topS rho / balancedCapDen rho r := by
  unfold balancedCap
  exact Real.sq_sqrt (balancedCap_ratio_pos hrho hr).le

lemma balancedCap_pos {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < balancedCap rho r := by
  unfold balancedCap
  exact Real.sqrt_pos.2 (balancedCap_ratio_pos hrho hr)

lemma balancedCap_le_one {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho r ≤ 1 := by
  have hden := balancedCapDen_pos hrho hr
  have hratio : topS rho / balancedCapDen rho r ≤ 1 :=
    (div_le_one hden).2 (topS_le_balancedCapDen hrho hr)
  unfold balancedCap
  rw [Real.sqrt_le_one]
  exact hratio

lemma balancedCap_mem_Icc {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho r ∈ Icc (0 : ℝ) 1 :=
  ⟨(balancedCap_pos hrho hr).le, balancedCap_le_one hrho hr⟩

lemma balancedCap_mul_ray_mem_Ioo {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho r * r ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact mul_pos (balancedCap_pos hrho hr) hr.1
  · nlinarith [balancedCap_le_one hrho hr, balancedCap_pos hrho hr, hr.1, hr.2]

/-- The cap substitution makes the entropy denominator collapse to the
ratio used in the manuscript. -/
lemma one_sub_balancedCap_mul_ray_sq {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    1 - (balancedCap rho r * r) ^ 2 =
      (1 - r ^ 2) / balancedCapDen rho r := by
  have hden := (balancedCapDen_pos hrho hr).ne'
  rw [mul_pow, balancedCap_sq hrho hr]
  unfold topS topR
  unfold balancedCapDen at hden ⊢
  field_simp [hden]
  ring_nf

/-- Once the cap residual is nonnegative, strict monotonicity of `G` places
the unique balanced root below the explicit cap. -/
theorem balancedRoot_le_cap_of_residual_nonneg
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hroot : balancedResidual rho c r = 0)
    (hcap : 0 ≤ balancedResidual rho (balancedCap rho r) r) :
    c ≤ balancedCap rho r := by
  by_contra hnot
  have hlt : balancedCap rho r < c := lt_of_not_ge hnot
  have hmono := balancedResidual_strictMonoOn
    (show rho ∈ Icc (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2.le⟩) hr
  have hstrict := hmono (balancedCap_mem_Icc hrho hr) hc hlt
  change balancedResidual rho (balancedCap rho r) r < balancedResidual rho c r at hstrict
  rw [hroot] at hstrict
  linarith

/-- Squared form of the cap reduction, matching the manuscript statement. -/
theorem balancedRoot_sq_le_capRatio_of_residual_nonneg
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hroot : balancedResidual rho c r = 0)
    (hcap : 0 ≤ balancedResidual rho (balancedCap rho r) r) :
    c ^ 2 ≤ topS rho / balancedCapDen rho r := by
  have hle := balancedRoot_le_cap_of_residual_nonneg hrho hr hc hroot hcap
  rw [← balancedCap_sq hrho hr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (add_nonneg hc.1 (balancedCap_pos hrho hr).le)]

end CourtadeKumar
