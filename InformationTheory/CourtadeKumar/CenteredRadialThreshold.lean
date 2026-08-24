import InformationTheory.CourtadeKumar.RadialEulerShapeMonotonicity

/-! The unique centered-contact shape threshold. -/

open Set Filter
open scoped NNReal

namespace CourtadeKumar

theorem radialEulerLogRatio_centered_zero
    {rho : ℝ} :
    radialEulerLogRatio rho 0 (1 / 2) = 1 := by
  have harg : radialEulerLogArg 1 0 (1 / 2) ∈ Ioo (0 : ℝ) 1 := by
    unfold radialEulerLogArg
    norm_num
  have hden := (radialEulerLog_pos_of_arg harg).ne'
  unfold radialEulerLogRatio
  have heq : radialEulerLog rho 0 (1 / 2) = radialEulerLog 1 0 (1 / 2) := by
    unfold radialEulerLog radialEulerLogArg
    ring
  rw [heq]
  exact div_self hden

theorem tendsto_radialEulerLogRatio_centered_zero_right
    {rho : ℝ} :
    Tendsto (fun r ↦ radialEulerLogRatio rho r (1 / 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
  have hargR : radialEulerLogArg rho 0 (1 / 2) ≠ 0 := by
    unfold radialEulerLogArg
    norm_num
  have harg1 : radialEulerLogArg 1 0 (1 / 2) ≠ 0 := by
    unfold radialEulerLogArg
    norm_num
  have hden : radialEulerLog 1 0 (1 / 2) ≠ 0 := by
    apply (radialEulerLog_pos_of_arg ?_).ne'
    unfold radialEulerLogArg
    norm_num
  have hcont := (hasDerivAt_radialEulerLogRatio_shape hargR harg1 hden).continuousAt.mono_left
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa only [radialEulerLogRatio_centered_zero] using hcont

theorem tendsto_radialEulerLogRatio_centered_one_left
    {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun r ↦ radialEulerLogRatio rho r (1 / 2))
      (nhdsWithin 1 (Iio (1 : ℝ))) (nhds 0) := by
  let l : Filter ℝ := nhdsWithin 1 (Iio (1 : ℝ))
  have hargAt : radialEulerLogArg 1 1 (1 / 2) = 0 := by
    unfold radialEulerLogArg
    norm_num
  have hargContinuous : Continuous (fun r ↦ radialEulerLogArg 1 r (1 / 2)) := by
    unfold radialEulerLogArg
    fun_prop
  have hargNhds : Tendsto (fun r ↦ radialEulerLogArg 1 r (1 / 2)) l (nhds 0) := by
    rw [← hargAt]
    exact hargContinuous.continuousAt.mono_left inf_le_left
  have hrpos : ∀ᶠ r in l, 0 < r := by
    change Ioi 0 ∈ nhds 1 ⊓ principal (Iio 1)
    exact mem_inf_of_left (Ioi_mem_nhds zero_lt_one)
  have hargPos : ∀ᶠ r in l, radialEulerLogArg 1 r (1 / 2) ∈ Ioi (0 : ℝ) := by
    filter_upwards [hrpos, self_mem_nhdsWithin] with r hr0 hr1
    have hrlt : r < 1 := hr1
    exact (radialEulerLogArg_order_physical
      (rho := (0 : ℝ)) (r := r) (z := (1 / 2 : ℝ))
      (by norm_num) hr0 (by norm_num) (by nlinarith)).1.1
  have hargTendsto : Tendsto (fun r ↦ radialEulerLogArg 1 r (1 / 2)) l
      (nhdsWithin 0 (Ioi (0 : ℝ))) :=
    tendsto_nhdsWithin_iff.2 ⟨hargNhds, hargPos⟩
  have hlog : Tendsto
      (fun r ↦ Real.log (radialEulerLogArg 1 r (1 / 2))) l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hargTendsto
  have hden : Tendsto (fun r ↦ radialEulerLog 1 r (1 / 2)) l atTop := by
    unfold radialEulerLog
    exact hlog.const_mul_atBot_of_neg (by norm_num)
  have hrhoplus : 0 < 1 + rho := by linarith [hrho.1]
  have hrhosq : rho ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.2 hrho.2) hrhoplus]
  have hargR : 0 < radialEulerLogArg rho 1 (1 / 2) := by
    unfold radialEulerLogArg
    nlinarith
  have hnum : Tendsto (fun r ↦ radialEulerLog rho r (1 / 2)) l
      (nhds (radialEulerLog rho 1 (1 / 2))) :=
    (hasDerivAt_radialEulerLog_shape hargR.ne').continuousAt.mono_left inf_le_left
  unfold radialEulerLogRatio
  exact hnum.div_atTop hden

/-- The centered multiplier assumes every interior value exactly once. -/
theorem existsUnique_centeredRadialShape
    {rho theta : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    ∃! r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧
      radialEulerLogRatio rho r (1 / 2) = theta := by
  let l0 : Filter ℝ := nhdsWithin 0 (Ioi (0 : ℝ))
  have hleftValue : ∀ᶠ r in l0,
      theta < radialEulerLogRatio rho r (1 / 2) :=
    tendsto_radialEulerLogRatio_centered_zero_right.eventually_const_lt htheta.2
  have hleftOne : ∀ᶠ r in l0, r < 1 := by
    have hid : Tendsto (id : ℝ → ℝ) l0 (nhds 0) := tendsto_id.mono_left inf_le_left
    simpa only [id_eq] using hid.eventually_lt_const zero_lt_one
  have hleftZero : ∀ᶠ r in l0, 0 < r := self_mem_nhdsWithin
  obtain ⟨a, haValue, ha0, ha1⟩ :=
    (hleftValue.and (hleftZero.and hleftOne)).exists
  let l1 : Filter ℝ := nhdsWithin 1 (Iio (1 : ℝ))
  have hrightValue : ∀ᶠ r in l1,
      radialEulerLogRatio rho r (1 / 2) < theta :=
    (tendsto_radialEulerLogRatio_centered_one_left hrho).eventually_lt_const htheta.1
  have hrightZero : ∀ᶠ r in l1, 0 < r := by
    have hid : Tendsto (id : ℝ → ℝ) l1 (nhds 1) := tendsto_id.mono_left inf_le_left
    simpa only [id_eq] using hid.eventually_const_lt zero_lt_one
  have hrightOne : ∀ᶠ r in l1, r < 1 := self_mem_nhdsWithin
  obtain ⟨b, hbValue, hb0, hb1⟩ :=
    (hrightValue.and (hrightZero.and hrightOne)).exists
  have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨ha0, ha1⟩
  have hb : b ∈ Ioo (0 : ℝ) 1 := ⟨hb0, hb1⟩
  have hanti := centeredRadialMultiplier_strictAntiOn hrho
  have hab : a < b := by
    by_contra hn
    have hba : b ≤ a := le_of_not_gt hn
    rcases hba.eq_or_lt with hbaeq | hba
    · subst b
      linarith
    · linarith [hanti hb ha hba]
  have hcont : ContinuousOn (fun r ↦ radialEulerLogRatio rho r (1 / 2))
      (Icc a b) := by
    intro r hrab
    have hr : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha0.trans_le hrab.1, hrab.2.trans_lt hb1⟩
    have hupper : (1 + r) * (1 / 2 : ℝ) < 1 := by nlinarith [hr.2]
    obtain ⟨harg1, hargR, _⟩ := radialEulerLogArg_order_physical
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
      hr.1 (by norm_num) hupper
    have hden := (radialEulerLog_pos_of_arg
      ⟨harg1.1, harg1.2.trans (by norm_num)⟩).ne'
    exact (hasDerivAt_radialEulerLogRatio_shape
      hargR.1.ne' harg1.1.ne' hden).continuousAt.continuousWithinAt
  have hthetaRange : theta ∈ Icc
      (radialEulerLogRatio rho b (1 / 2))
      (radialEulerLogRatio rho a (1 / 2)) := ⟨hbValue.le, haValue.le⟩
  obtain ⟨r, hrab, hrValue⟩ := intermediate_value_Icc' hab.le hcont hthetaRange
  have hr : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha0.trans_le hrab.1, hrab.2.trans_lt hb1⟩
  refine ⟨r, ⟨hr, hrValue⟩, ?_⟩
  intro s hs
  exact hanti.injOn hs.1 hr (hs.2.trans hrValue.symm)

theorem canonicalRadialContactZ_eq_half_of_centeredRoot
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ)) rstar (1 / 2) = theta) :
    canonicalRadialContactZ alpha theta halpha htheta rstar = 1 / 2 := by
  have hzspec := canonicalRadialContactZ_spec halpha htheta hrstar.1
  exact (existsUnique_radialEulerLogRatio_eq
    (channelRho_mem_Ico_of_alpha_interior halpha) htheta hrstar.1).unique
      ⟨hzspec.1, hzspec.2⟩
      ⟨by
        constructor
        · norm_num
        · rw [inv_eq_one_div]
          exact (lt_div_iff₀ (by linarith [hrstar.1])).2 (by nlinarith [hrstar.2]),
       hcenter⟩

theorem canonicalRadialProfile_centeredContact
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ)) rstar (1 / 2) = theta) :
    canonicalRadialProfile alpha theta halpha htheta rstar =
      2 * radialTriangleDifference alpha theta rstar (1 / 2) := by
  rw [canonicalRadialProfile]
  simp only [if_pos hrstar.1]
  rw [canonicalRadialContactZ_eq_half_of_centeredRoot
    halpha htheta hrstar hcenter]
  ring

end CourtadeKumar
