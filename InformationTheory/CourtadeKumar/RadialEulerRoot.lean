import InformationTheory.CourtadeKumar.RadialEulerEndpointLimits

/-! Existence and uniqueness of the radial Euler contact root. -/

open Set Filter

namespace CourtadeKumar

theorem continuousOn_radialEulerLogRatio_physical
    {rho r : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : 0 < r) :
    ContinuousOn (radialEulerLogRatio rho r)
      (Ioo (0 : ℝ) (1 + r)⁻¹) := by
  intro z hz
  have h1r : 0 < 1 + r := by linarith
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
      _ = 1 := inv_mul_cancel₀ h1r.ne'
  obtain ⟨harg1, hargR, _⟩ :=
    radialEulerLogArg_order_physical hrho hr hz.1 hupper
  have hq1 : 1 - z < 1 := by linarith [hz.1]
  have hden : radialEulerLog 1 r z ≠ 0 :=
    (radialEulerLog_pos_of_arg ⟨harg1.1, harg1.2.trans hq1⟩).ne'
  exact (hasDerivAt_radialEulerLogRatio hargR.1.ne' harg1.1.ne' hden).continuousAt
    |>.continuousWithinAt

/-- Every multiplier strictly between zero and one has a unique contact on
each nondegenerate radial cell. -/
theorem existsUnique_radialEulerLogRatio_eq
    {rho theta r : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) :
    ∃! z : ℝ, z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ ∧
      radialEulerLogRatio rho r z = theta := by
  let cap : ℝ := (1 + r)⁻¹
  have h1r : 0 < 1 + r := by linarith
  have hcap : 0 < cap := by
    dsimp [cap]
    exact inv_pos.2 h1r
  let l0 : Filter ℝ := nhdsWithin 0 (Ioi (0 : ℝ))
  have hleftValue : ∀ᶠ z in l0, theta < radialEulerLogRatio rho r z :=
    (tendsto_radialEulerLogRatio_zero_right rho r).eventually_const_lt htheta.2
  have hleftCap : ∀ᶠ z in l0, z < cap := by
    have hid : Tendsto (id : ℝ → ℝ) l0 (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    simpa only [id_eq] using hid.eventually_lt_const hcap
  have hleftDomain : ∀ᶠ z in l0, 0 < z := self_mem_nhdsWithin
  obtain ⟨a, haValue, ha0, haCap⟩ :=
    (hleftValue.and (hleftDomain.and hleftCap)).exists
  let lc : Filter ℝ := nhdsWithin cap (Iio cap)
  have hrightValue : ∀ᶠ z in lc, radialEulerLogRatio rho r z < theta :=
    (tendsto_radialEulerLogRatio_outerEndpoint hrho hr).eventually_lt_const htheta.1
  have hrightZero : ∀ᶠ z in lc, 0 < z := by
    have hid : Tendsto (id : ℝ → ℝ) lc (nhds cap) :=
      tendsto_id.mono_left inf_le_left
    simpa only [id_eq] using hid.eventually_const_lt hcap
  have hrightCap : ∀ᶠ z in lc, z < cap := self_mem_nhdsWithin
  obtain ⟨b, hbValue, hb0, hbCap⟩ :=
    (hrightValue.and (hrightZero.and hrightCap)).exists
  have ha : a ∈ Ioo (0 : ℝ) cap := ⟨ha0, haCap⟩
  have hb : b ∈ Ioo (0 : ℝ) cap := ⟨hb0, hbCap⟩
  have hanti : StrictAntiOn (radialEulerLogRatio rho r) (Ioo (0 : ℝ) cap) := by
    dsimp [cap]
    exact radialEulerLogRatio_strictAntiOn_physical hrho hr
  have hab : a < b := by
    by_contra hn
    have hba : b ≤ a := le_of_not_gt hn
    rcases hba.eq_or_lt with hbaeq | hba
    · subst b
      linarith
    · have := hanti hb ha hba
      linarith
  have hcont : ContinuousOn (radialEulerLogRatio rho r) (Icc a b) :=
    (continuousOn_radialEulerLogRatio_physical hrho hr).mono (by
      intro z hz
      exact ⟨ha0.trans_le hz.1, hz.2.trans_lt hbCap⟩)
  have hthetaRange : theta ∈ Icc
      (radialEulerLogRatio rho r b) (radialEulerLogRatio rho r a) :=
    ⟨hbValue.le, haValue.le⟩
  obtain ⟨z, hzab, hzValue⟩ :=
    intermediate_value_Icc' hab.le hcont hthetaRange
  have hz : z ∈ Ioo (0 : ℝ) cap :=
    ⟨ha0.trans_le hzab.1, hzab.2.trans_lt hbCap⟩
  refine ⟨z, ⟨hz, hzValue⟩, ?_⟩
  intro w hw
  exact hanti.injOn hw.1 hz (hw.2.trans hzValue.symm)

end CourtadeKumar
