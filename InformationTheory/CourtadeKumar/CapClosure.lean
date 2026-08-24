import InformationTheory.CourtadeKumar.CapAuxConcavity
import InformationTheory.CourtadeKumar.ReserveConcavity

open Set

namespace CourtadeKumar

lemma artanh_eq_log_one_add_sub_half_log_one_sub_sq {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh x = Real.log (1 + x) - (1 / 2 : ℝ) * Real.log (1 - x ^ 2) := by
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hp : 0 < 1 + x := by linarith [hx.1]
  rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩]
  rw [Real.log_div hp.ne' hm.ne']
  have hprod : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
  calc
    _ = Real.log (1 + x) - (1 / 2 : ℝ) *
        (Real.log (1 - x) + Real.log (1 + x)) := by ring
    _ = Real.log (1 + x) - (1 / 2 : ℝ) *
        Real.log ((1 - x) * (1 + x)) := by rw [Real.log_mul hm.ne' hp.ne']
    _ = _ := by rw [hprod]

/-- A continuous rearrangement of `F` at the singular ray endpoint. -/
noncomputable def balancedCapAuxFRegular (rho r : ℝ) : ℝ :=
  Real.log (1 + r) -
    topS rho * Real.log (1 + balancedCap rho r * r) -
    topS rho / 2 * Real.log (balancedCapDen rho r) -
    rho ^ 2 * r * Real.log 2 -
    2 * topEll rho * (balancedCap rho r * r) +
    rho ^ 2 / 2 *
      (Real.negMulLog (1 - r) - (1 - r) * Real.log (1 + r))

theorem balancedCapAuxFRegular_eq {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCapAuxFRegular rho r = balancedCapAuxF rho r := by
  have hrfull : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
  have hwmem := balancedCap_mul_ray_mem_Ioo hrho hr
  have hwfull : balancedCap rho r * r ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hwmem.1], hwmem.2⟩
  have hone : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hden := balancedCapDen_pos hrho hr
  have hratio := one_sub_balancedCap_mul_ray_sq hrho hr
  have hlogratio :
      Real.log (1 - (balancedCap rho r * r) ^ 2) =
        Real.log (1 - r ^ 2) - Real.log (balancedCapDen rho r) := by
    rw [hratio, Real.log_div hone.ne' hden.ne']
  have hm : 0 < 1 - r := by linarith [hr.2]
  have hp : 0 < 1 + r := by linarith [hr.1]
  have htail :
      Real.negMulLog (1 - r) - (1 - r) * Real.log (1 + r) =
        (r - 1) * Real.log (1 - r ^ 2) := by
    rw [Real.negMulLog_eq_neg]
    change
      -((1 - r) * Real.log (1 - r)) - (1 - r) * Real.log (1 + r) =
        (r - 1) * Real.log (1 - r ^ 2)
    have hprod : (1 - r) * (1 + r) = 1 - r ^ 2 := by ring
    calc
      _ = -(1 - r) * (Real.log (1 - r) + Real.log (1 + r)) := by ring
      _ = -(1 - r) * Real.log ((1 - r) * (1 + r)) := by
        rw [Real.log_mul hm.ne' hp.ne']
      _ = _ := by rw [hprod]; ring
  unfold balancedCapAuxFRegular balancedCapAuxF topL0
  rw [artanh_eq_log_one_add_sub_half_log_one_sub_sq hrfull,
    artanh_eq_log_one_add_sub_half_log_one_sub_sq hwfull,
    hlogratio, htail]
  unfold topS topR
  ring

lemma balancedCapDen_pos_Icc {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    0 < balancedCapDen rho r := by
  unfold balancedCapDen
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  have hrho2 : rho ^ 2 < 1 := by nlinarith [hrho.1, hrho.2]
  nlinarith [mul_le_mul_of_nonneg_left hr2 (sq_nonneg rho)]

lemma continuousAt_balancedCap_Icc {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (balancedCap rho) r := by
  have hden := (balancedCapDen_pos_Icc hrho hr).ne'
  unfold balancedCap
  apply Real.continuous_sqrt.continuousAt.comp
  exact continuousAt_const.div (by unfold balancedCapDen; fun_prop) hden

theorem continuousOn_balancedCapAuxFRegular {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (balancedCapAuxFRegular rho) (Icc (0 : ℝ) 1) := by
  intro r hr
  have hc := continuousAt_balancedCap_Icc hrho hr
  have hdenAt : ContinuousAt (balancedCapDen rho) r := by
    unfold balancedCapDen
    fun_prop
  have hdenpos := balancedCapDen_pos_Icc hrho hr
  have hplusr : 1 + r ≠ 0 := by linarith [hr.1]
  have hplusw : 1 + balancedCap rho r * r ≠ 0 := by
    have hc0 : 0 ≤ balancedCap rho r := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hc0 hr.1]
  have hwAt : ContinuousAt (fun z ↦ balancedCap rho z * z) r := hc.mul continuousAt_id
  have hlogr : ContinuousAt (fun z : ℝ ↦ Real.log (1 + z)) r :=
    (Real.continuousAt_log hplusr).comp (continuousAt_const.add continuousAt_id)
  have hpluswAt : ContinuousAt (fun z ↦ 1 + balancedCap rho z * z) r :=
    continuousAt_const.add hwAt
  have hlogw : ContinuousAt
      (fun z ↦ Real.log (1 + balancedCap rho z * z)) r :=
    (Real.continuousAt_log hplusw).comp_of_eq hpluswAt rfl
  have hlogden : ContinuousAt (fun z ↦ Real.log (balancedCapDen rho z)) r :=
    (Real.continuousAt_log hdenpos.ne').comp hdenAt
  have hneg : ContinuousAt (fun z : ℝ ↦ Real.negMulLog (1 - z)) r :=
    Real.continuous_negMulLog.continuousAt.comp (continuousAt_const.sub continuousAt_id)
  unfold balancedCapAuxFRegular
  exact (((((hlogr.sub (continuousAt_const.mul hlogw)).sub
      ((continuousAt_const.div_const 2).mul hlogden)).sub
      ((continuousAt_const.mul continuousAt_id).mul continuousAt_const)).sub
      (continuousAt_const.mul hwAt)).add
      ((continuousAt_const.div_const 2).mul
        (hneg.sub ((continuousAt_const.sub continuousAt_id).mul hlogr)))).continuousWithinAt

lemma balancedCap_zero (rho : ℝ) :
    balancedCap rho 0 = Real.sqrt (topS rho) := by
  simp [balancedCap, balancedCapDen]

lemma balancedCap_one {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho 1 = 1 := by
  have hs : 1 - rho ^ 2 ≠ 0 := by nlinarith [hrho.1, hrho.2]
  unfold balancedCap balancedCapDen topS topR
  rw [show 1 - rho ^ 2 * 1 ^ 2 = 1 - rho ^ 2 by ring]
  rw [div_self hs, Real.sqrt_one]

@[simp] lemma balancedCapAuxFRegular_zero (rho : ℝ) :
    balancedCapAuxFRegular rho 0 = 0 := by
  simp [balancedCapAuxFRegular, balancedCapDen]

lemma balancedCapAuxFRegular_one {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    balancedCapAuxFRegular rho 1 =
      -topS rho / 2 * Real.log (topS rho) - 2 * topEll rho := by
  rw [balancedCapAuxFRegular, balancedCap_one hrho]
  unfold balancedCapDen topS topR
  simp
  ring_nf

theorem balancedCapAuxFRegular_concaveOn {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (balancedCapAuxFRegular rho) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (continuousOn_balancedCapAuxFRegular hrho)
  · intro r hr
    rw [interior_Icc] at hr
    refine (hasDerivAt_balancedCapAuxF hrho hr).hasDerivWithinAt.congr ?_ ?_
    · intro z hz
      exact balancedCapAuxFRegular_eq hrho (by simpa only [interior_Icc] using hz)
    · exact balancedCapAuxFRegular_eq hrho hr
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_balancedCapAuxFDeriv hrho hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact balancedCapAuxFDeriv2_nonpos hrho hr

lemma balancedCapAuxFRegular_one_nonneg {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    0 ≤ balancedCapAuxFRegular rho 1 := by
  rw [balancedCapAuxFRegular_one hrho]
  have hchannel := topEll_le_channelCap
    (show rho ∈ Icc (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2.le⟩)
  nlinarith

theorem balancedCapAuxFRegular_nonneg {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ balancedCapAuxFRegular rho r :=
  concaveOn_nonneg_of_endpoints (balancedCapAuxFRegular_concaveOn hrho)
    (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp)
    hr.1 hr.2 (by simp) (balancedCapAuxFRegular_one_nonneg hrho)

theorem balancedCapAuxF_nonneg {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 ≤ balancedCapAuxF rho r := by
  rw [← balancedCapAuxFRegular_eq hrho hr]
  exact balancedCapAuxFRegular_nonneg hrho ⟨hr.1.le, hr.2.le⟩

theorem continuousOn_balancedCapResidual {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (balancedCapResidual rho) (Icc (0 : ℝ) 1) := by
  intro r hr
  have hc := continuousAt_balancedCap_Icc hrho hr
  have hw : ContinuousAt (fun z ↦ balancedCap rho z * z) r := hc.mul continuousAt_id
  have hJ : Continuous topJ := continuous_const.sub continuous_topPhi
  have hJw : ContinuousAt (fun z ↦ topJ (balancedCap rho z * z)) r :=
    hJ.continuousAt.comp_of_eq hw rfl
  unfold balancedCapResidual balancedResidual
  exact (((hc.mul hJ.continuousAt).sub
    (continuousAt_const.mul hJw)).sub
    (continuousAt_const.mul
      (continuousAt_const.sub ((hc.pow 2).mul (continuousAt_id.pow 2))))).continuousWithinAt

@[simp] lemma balancedCapResidual_one {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    balancedCapResidual rho 1 = 0 := by
  unfold balancedCapResidual balancedResidual
  rw [balancedCap_one hrho]
  simp [topJ, topPhi]

theorem balancedCapResidual_antitoneOn {rho : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn (balancedCapResidual rho) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    (continuousOn_balancedCapResidual hrho)
  · intro r hr
    rw [interior_Icc] at hr
    exact (hasDerivAt_balancedCapResidual hrho hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    have hfactor : -(balancedCap rho r / balancedCapDen rho r) ≤ 0 := by
      exact neg_nonpos.mpr (div_nonneg (balancedCap_pos hrho hr).le
        (balancedCapDen_pos hrho hr).le)
    exact mul_nonpos_of_nonpos_of_nonneg hfactor (balancedCapAuxF_nonneg hrho hr)

/-- The explicit cap residual is nonnegative, completing the analytic cap
argument. -/
theorem balancedCapResidual_nonneg {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ balancedCapResidual rho r := by
  have h := balancedCapResidual_antitoneOn hrho hr
    (show (1 : ℝ) ∈ Icc 0 1 by simp) hr.2
  rw [balancedCapResidual_one hrho] at h
  exact h

/-- The corrected balanced root satisfies the explicit manuscript cap. -/
theorem balancedRoot_sq_le_capRatio
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hroot : balancedResidual rho c r = 0) :
    c ^ 2 ≤ topS rho / balancedCapDen rho r := by
  apply balancedRoot_sq_le_capRatio_of_residual_nonneg hrho hr hc hroot
  exact balancedCapResidual_nonneg hrho ⟨hr.1.le, hr.2.le⟩

end CourtadeKumar
