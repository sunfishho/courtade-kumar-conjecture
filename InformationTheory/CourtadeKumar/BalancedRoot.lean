import InformationTheory.CourtadeKumar.EnergyPositivity

/-! Existence and uniqueness of the corrected TOP balanced contact. -/

open Set

namespace CourtadeKumar

lemma topJ_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < topJ x := by
  rw [topJ_eq_binEntropy]
  apply Real.binEntropy_pos <;> linarith [hx.1, hx.2]

lemma topPhi_pos {x : ℝ} (hx0 : x ≠ 0) : 0 < topPhi x := by
  unfold topPhi
  rw [sub_pos, Real.binEntropy_lt_log_two]
  intro h
  norm_num at h
  exact hx0 h

theorem hasDerivAt_balancedResidual {rho c r : ℝ}
    (hcr : c * r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ balancedResidual rho x r)
      (topJ r + topS rho * r * Real.artanh (c * r) +
        2 * topEll rho * c * r ^ 2) c := by
  have hfirst : HasDerivAt (fun x : ℝ ↦ x * topJ r) (topJ r) c := by
    simpa using (hasDerivAt_id c).mul_const (topJ r)
  have harg : HasDerivAt (fun x : ℝ ↦ x * r) r c := by
    simpa using (hasDerivAt_id c).mul_const r
  have hj := (hasDerivAt_topJ hcr).comp c harg
  have hmiddle := hj.const_mul (topS rho)
  have hsquare := (hasDerivAt_id c).pow 2
  have hscaled := hsquare.mul_const (r ^ 2)
  have honeMinus := (hasDerivAt_const c 1).sub hscaled
  have hlast := honeMinus.const_mul (topEll rho)
  unfold balancedResidual
  convert (hfirst.sub hmiddle).sub hlast using 1
  simp [id_eq]
  ring_nf

lemma continuous_balancedResidual (rho r : ℝ) :
    Continuous (fun c ↦ balancedResidual rho c r) := by
  have hJ : Continuous topJ := continuous_const.sub continuous_topPhi
  unfold balancedResidual
  exact ((continuous_id.mul continuous_const).sub
    (continuous_const.mul (hJ.comp (continuous_id.mul continuous_const)))).sub
    (continuous_const.mul
      (continuous_const.sub ((continuous_id.pow 2).mul continuous_const)))

theorem balancedResidual_strictMonoOn
    {rho r : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (fun c ↦ balancedResidual rho c r) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact (continuous_balancedResidual rho r).continuousOn
  · intro c hc
    rw [interior_Icc] at hc
    have hcr : c * r ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [hc.1, hr.1]
      · nlinarith [hc.1, hc.2, hr.1, hr.2]
    rw [(hasDerivAt_balancedResidual hcr).deriv]
    have hj : 0 < topJ r := topJ_pos ⟨by linarith [hr.1], hr.2⟩
    have hs := topS_nonneg hrho
    have hell := topEll_nonneg hrho
    have ha : 0 ≤ Real.artanh (c * r) := Real.artanh_nonneg (mul_nonneg hc.1.le hr.1.le)
    have hterm1 : 0 ≤ topS rho * r * Real.artanh (c * r) :=
      mul_nonneg (mul_nonneg hs hr.1.le) ha
    have hterm2 : 0 ≤ 2 * topEll rho * c * r ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hell) hc.1.le) (sq_nonneg r)
    linarith

lemma balancedResidual_zero (rho r : ℝ) :
    balancedResidual rho 0 r = -topJ rho := by
  unfold balancedResidual topS topEll topR topJ
  simp [topPhi_zero]
  ring_nf

lemma balancedResidual_one_pos
    {rho r : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < balancedResidual rho 1 r := by
  have hrIcc : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1.le, hrho.2.le⟩
  have hellr := topEll_nonneg hrIcc
  have hJbound : (1 - r ^ 2) * Real.log 2 ≤ topJ r := by
    unfold topEll topR at hellr
    unfold topJ
    linarith
  have hphi : 0 < topPhi rho := topPhi_pos (ne_of_gt hrho.1)
  have hone : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hm := mul_le_mul_of_nonneg_left hJbound (sq_nonneg rho)
  have hid : rho ^ 2 * Real.log 2 - topEll rho = topPhi rho := by
    simp [topEll, topR]
  have heq : balancedResidual rho 1 r =
      rho ^ 2 * topJ r - topEll rho * (1 - r ^ 2) := by
    unfold balancedResidual topS topR
    ring_nf
  rw [heq]
  nlinarith [mul_pos hone hphi]

theorem existsUnique_balancedRoot
    {rho r : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃! c : ℝ, c ∈ Ioo (0 : ℝ) 1 ∧ balancedResidual rho c r = 0 := by
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1.le, hrho.2.le⟩
  have hmono := balancedResidual_strictMonoOn hrhoIcc hr
  have hzero : balancedResidual rho 0 r < 0 := by
    rw [balancedResidual_zero]
    exact neg_lt_zero.mpr (topJ_pos ⟨by linarith [hrho.1], hrho.2⟩)
  have hone := balancedResidual_one_pos hrho hr
  have hcont : ContinuousOn (fun c ↦ balancedResidual rho c r) (Icc (0 : ℝ) 1) :=
    (continuous_balancedResidual rho r).continuousOn
  obtain ⟨c, hcIcc, hc⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont
    (show (0 : ℝ) ∈ Icc (balancedResidual rho 0 r) (balancedResidual rho 1 r) by
      exact ⟨hzero.le, hone.le⟩)
  have hcIoo : c ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_not_ge fun hc0 ↦ by
        have : c = 0 := by linarith [hcIcc.1]
        subst c
        linarith
    · exact lt_of_not_ge fun hc1 ↦ by
        have : c = 1 := by linarith [hcIcc.2]
        subst c
        linarith
  refine ⟨c, ⟨hcIoo, hc⟩, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyc | hcy
  · have := hmono ⟨hy.1.1.le, hy.1.2.le⟩ ⟨hcIoo.1.le, hcIoo.2.le⟩ hyc
    linarith [hy.2, hc]
  · have := hmono ⟨hcIoo.1.le, hcIoo.2.le⟩ ⟨hy.1.1.le, hy.1.2.le⟩ hcy
    linarith [hy.2, hc]

end CourtadeKumar
