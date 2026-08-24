import InformationTheory.CourtadeKumar.CapAuxDerivative

/-! Concavity of the balanced-cap auxiliary function. -/

open Set

namespace CourtadeKumar

noncomputable def balancedCapAuxFDeriv2 (rho r : ℝ) : ℝ :=
  rho ^ 2 * r *
    (rho ^ 2 * balancedCap rho r / balancedCapDen rho r *
        (1 - 1 / (1 + balancedCap rho r) ^ 2) -
      1 / (1 - r ^ 2) -
      6 * topEll rho * balancedCap rho r / balancedCapDen rho r ^ 2)

theorem hasDerivAt_balancedCapAuxFDeriv {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (balancedCapAuxFDeriv rho) (balancedCapAuxFDeriv2 rho r) r := by
  have hc := hasDerivAt_balancedCap hrho hr
  have hdenpos := balancedCapDen_pos hrho hr
  have hdenne := hdenpos.ne'
  have hden : HasDerivAt (balancedCapDen rho) (-2 * rho ^ 2 * r) r := by
    unfold balancedCapDen
    convert (hasDerivAt_const r 1).sub
      ((hasDerivAt_const r (rho ^ 2)).mul ((hasDerivAt_id r).pow 2)) using 1
    simp [id_eq]
    ring_nf
  have honeplus : 1 + balancedCap rho r ≠ 0 := by
    nlinarith [balancedCap_pos hrho hr]
  have honeplusDeriv := (hasDerivAt_const r 1).add hc
  have hinv := (hasDerivAt_const r 1).div honeplusDeriv honeplus
  have hL0 := hasDerivAt_topL0
    (show r ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hr.1], hr.2⟩)
  have hbracket := (((hc.add hinv).sub_const (Real.log 2)).sub hL0).const_mul (rho ^ 2)
  have hratio := hc.div hden hdenne |>.const_mul (2 * topEll rho)
  have htotal := hbracket.sub hratio
  unfold balancedCapAuxFDeriv balancedCapAuxFDeriv2
  convert htotal using 1
  · funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.div_apply]
    ring_nf
  · simp only [Pi.add_apply, zero_add, zero_mul, one_mul]
    field_simp [hdenne, honeplus]
    ring_nf

lemma balancedCap_shapeFactor_nonneg {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 ≤ 1 - 1 / (1 + balancedCap rho r) ^ 2 := by
  have hc := (balancedCap_pos hrho hr).le
  have hsq : 1 ≤ (1 + balancedCap rho r) ^ 2 := by nlinarith
  have hpos : 0 < (1 + balancedCap rho r) ^ 2 := by positivity
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsq
  norm_num at h
  exact sub_nonneg.mpr (by simpa [one_div] using h)

lemma balancedCap_mul_shapeFactor_lt_one {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho r * (1 - 1 / (1 + balancedCap rho r) ^ 2) < 1 := by
  have hc0 := (balancedCap_pos hrho hr).le
  have hc1 := balancedCap_le_one hrho hr
  have hinvpos : 0 < 1 / (1 + balancedCap rho r) ^ 2 := by positivity
  have hfactor := balancedCap_shapeFactor_nonneg hrho hr
  have hfactorlt : 1 - 1 / (1 + balancedCap rho r) ^ 2 < 1 := by linarith
  exact (mul_le_of_le_one_left hfactor hc1).trans_lt hfactorlt

lemma channelRatio_le_rayReciprocal {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    rho ^ 2 / balancedCapDen rho r ≤ 1 / (1 - r ^ 2) := by
  have hden := balancedCapDen_pos hrho hr
  have hone : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  apply (div_le_div_iff₀ hden hone).2
  unfold balancedCapDen
  nlinarith [mul_pos (sub_pos.mpr hrho.2) (add_pos_of_pos_of_nonneg hrho.1 zero_le_one)]

theorem balancedCapAuxFDeriv2_nonpos {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCapAuxFDeriv2 rho r ≤ 0 := by
  have hratio := channelRatio_le_rayReciprocal hrho hr
  have hshape := balancedCap_mul_shapeFactor_lt_one hrho hr
  have hshape0 := balancedCap_shapeFactor_nonneg hrho hr
  have hden := balancedCapDen_pos hrho hr
  have hone : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hell := topEll_nonneg
    (show rho ∈ Icc (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2.le⟩)
  have hfirst :
      rho ^ 2 * balancedCap rho r / balancedCapDen rho r *
          (1 - 1 / (1 + balancedCap rho r) ^ 2) ≤
        1 / (1 - r ^ 2) := by
    calc
      _ = (rho ^ 2 / balancedCapDen rho r) *
          (balancedCap rho r * (1 - 1 / (1 + balancedCap rho r) ^ 2)) := by ring
      _ ≤ (1 / (1 - r ^ 2)) *
          (balancedCap rho r * (1 - 1 / (1 + balancedCap rho r) ^ 2)) :=
        mul_le_mul_of_nonneg_right hratio (mul_nonneg (balancedCap_pos hrho hr).le hshape0)
      _ ≤ 1 / (1 - r ^ 2) := by
        exact mul_le_of_le_one_right (one_div_nonneg.mpr hone.le) hshape.le
  unfold balancedCapAuxFDeriv2
  have hlast : 0 ≤
      6 * topEll rho * balancedCap rho r / balancedCapDen rho r ^ 2 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hell) (balancedCap_pos hrho hr).le)
      (sq_nonneg (balancedCapDen rho r))
  have hRr : 0 ≤ rho ^ 2 * r := mul_nonneg (sq_nonneg rho) hr.1.le
  exact mul_nonpos_of_nonneg_of_nonpos hRr (by linarith)

/-- The manuscript's auxiliary function is concave throughout the open ray
interval.  Endpoint values are handled by continuous extension separately. -/
theorem balancedCapAuxF_concaveOn_Ioo {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (balancedCapAuxF rho) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioo 0 1)
  · intro r hr
    exact (hasDerivAt_balancedCapAuxF hrho hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hasDerivAt_balancedCapAuxF hrho hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hasDerivAt_balancedCapAuxFDeriv hrho hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact balancedCapAuxFDeriv2_nonpos hrho hr

end CourtadeKumar
