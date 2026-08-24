import InformationTheory.CourtadeKumar.RadialEulerCrossSign

/-! Unimodality of the radial perspective quotient from Euler-ratio monotonicity. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- All four entropy arguments lie in the genuine interior of the binary
entropy domain at an interior point of a nondegenerate ray. -/
theorem radialEntropyArgs_physical
    {rho r z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹) :
    (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1 ∧
      (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1 ∧
      (1 - r) * z ∈ Ioo (0 : ℝ) 1 ∧
      (1 + r) * z ∈ Ioo (0 : ℝ) 1 := by
  have h1r : 0 < 1 + r := add_pos_of_pos_of_nonneg zero_lt_one hr.1.le
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
      _ = 1 := inv_mul_cancel₀ h1r.ne'
  have hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (sub_pos.2 hr.2) hz.1
    · nlinarith [mul_pos hr.1 hz.1]
  have hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos h1r hz.1, hupper⟩
  have hrhor_nonneg : 0 ≤ rho * r := mul_nonneg hrho.1 hr.1.le
  have hrhor_le_r : rho * r ≤ r := by
    nlinarith [mul_nonneg (sub_nonneg.2 hrho.2) hr.1.le]
  have hrhor_lt : rho * r < 1 := hrhor_le_r.trans_lt hr.2
  have hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (sub_pos.2 hrhor_lt) hz.1
    · exact (mul_le_mul_of_nonneg_right (by linarith [hrhor_nonneg, hr.1]) hz.1.le).trans_lt
        hplus.2
  have hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (by linarith) hz.1
    · exact (mul_le_mul_of_nonneg_right (by linarith [hrhor_le_r]) hz.1.le).trans_lt
        hplus.2
  exact ⟨hRminus, hRplus, hminus, hplus⟩

theorem channelRho_mem_Ico_of_alpha_interior
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    channelRho (alpha : ℝ) ∈ Ico (0 : ℝ) 1 := by
  unfold channelRho
  constructor <;> linarith [halpha.1, halpha.2]

theorem channelRho_mem_Icc_of_alpha_interior
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    channelRho (alpha : ℝ) ∈ Icc (0 : ℝ) 1 :=
  ⟨(channelRho_mem_Ico_of_alpha_interior halpha).1,
    (channelRho_mem_Ico_of_alpha_interior halpha).2.le⟩

/-- Before an interior stationary contact, the perspective quotient has
strictly negative derivative. -/
theorem deriv_radialTriangleDifference_div_neg_before_stationary
    {alpha : ℝ≥0} {theta r z w : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hw : w ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hwz : w < z)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect (channelRho (alpha : ℝ)) r z = 0) :
    deriv (fun t ↦ radialTriangleDifference alpha theta r t / t) w < 0 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrhoIco : rho ∈ Ico (0 : ℝ) 1 :=
    channelRho_mem_Ico_of_alpha_interior halpha
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrhoIco.1, hrhoIco.2.le⟩
  obtain ⟨hRminusW, hRplusW, hminusW, hplusW⟩ :=
    radialEntropyArgs_physical hrhoIcc hr hw
  obtain ⟨_, _, hminusZ, hplusZ⟩ :=
    radialEntropyArgs_physical hrhoIcc hr hz
  have hratioZ : radialEulerRatio rho r z = theta :=
    (radial_stationary_iff_ratio hminusZ hplusZ).1 hstat
  have hratio : theta < radialEulerRatio rho r w := by
    rw [← hratioZ]
    exact (radialEulerRatio_strictAntiOn_physical hrhoIco hr) hw hz hwz
  have hD : 0 < radialEulerDefect 1 r w :=
    radialEulerDefect_pos (by simpa using hminusW) (by simpa using hplusW)
  have hnum : theta * radialEulerDefect 1 r w -
      radialEulerDefect rho r w < 0 := by
    unfold radialEulerRatio at hratio
    have := (lt_div_iff₀ hD).1 hratio
    linarith
  have hderiv := hasDerivAt_radialTriangleDifference_div
    (alpha := alpha) (theta := theta) hw.1.ne'
    hRminusW hRplusW hminusW hplusW
  rw [hderiv.deriv]
  exact div_neg_of_neg_of_pos hnum
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hw.1))

/-- After an interior stationary contact, the perspective quotient has
strictly positive derivative. -/
theorem deriv_radialTriangleDifference_div_pos_after_stationary
    {alpha : ℝ≥0} {theta r z w : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hw : w ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hzw : z < w)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect (channelRho (alpha : ℝ)) r z = 0) :
    0 < deriv (fun t ↦ radialTriangleDifference alpha theta r t / t) w := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrhoIco : rho ∈ Ico (0 : ℝ) 1 :=
    channelRho_mem_Ico_of_alpha_interior halpha
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrhoIco.1, hrhoIco.2.le⟩
  obtain ⟨hRminusW, hRplusW, hminusW, hplusW⟩ :=
    radialEntropyArgs_physical hrhoIcc hr hw
  obtain ⟨_, _, hminusZ, hplusZ⟩ :=
    radialEntropyArgs_physical hrhoIcc hr hz
  have hratioZ : radialEulerRatio rho r z = theta :=
    (radial_stationary_iff_ratio hminusZ hplusZ).1 hstat
  have hratio : radialEulerRatio rho r w < theta := by
    rw [← hratioZ]
    exact (radialEulerRatio_strictAntiOn_physical hrhoIco hr) hz hw hzw
  have hD : 0 < radialEulerDefect 1 r w :=
    radialEulerDefect_pos (by simpa using hminusW) (by simpa using hplusW)
  have hnum : 0 < theta * radialEulerDefect 1 r w -
      radialEulerDefect rho r w := by
    unfold radialEulerRatio at hratio
    have := (div_lt_iff₀ hD).1 hratio
    linarith
  have hderiv := hasDerivAt_radialTriangleDifference_div
    (alpha := alpha) (theta := theta) hw.1.ne'
    hRminusW hRplusW hminusW hplusW
  rw [hderiv.deriv]
  exact div_pos hnum
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hw.1))

theorem continuous_radialTriangleDifference
    (alpha : ℝ≥0) (theta r : ℝ) :
    Continuous (radialTriangleDifference alpha theta r) := by
  unfold radialTriangleDifference radialTriangleChannelEntropy
    radialTriangleEntropy binaryEntropyBits
  fun_prop

/-- An interior Euler-stationary contact is the global minimum of the
perspective quotient on its whole radial cell, including the closed outer
endpoint. -/
theorem radialTriangleDifference_div_min_of_stationary
    {alpha : ℝ≥0} {theta r z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect (channelRho (alpha : ℝ)) r z = 0) :
    ∀ w : ℝ, 0 < w → w ≤ (1 + r)⁻¹ →
      radialTriangleDifference alpha theta r z / z ≤
        radialTriangleDifference alpha theta r w / w := by
  intro w hw0 hwcap
  let f : ℝ → ℝ := fun t ↦ radialTriangleDifference alpha theta r t / t
  have hrho : channelRho (alpha : ℝ) ∈ Icc (0 : ℝ) 1 :=
    channelRho_mem_Icc_of_alpha_interior halpha
  have hcontinuous : ∀ {a b : ℝ}, 0 < a →
      ContinuousOn f (Icc a b) := by
    intro a b ha t ht
    exact ((continuous_radialTriangleDifference alpha theta r).continuousAt.div
      continuousAt_id (by simpa only [id_eq] using
        (ne_of_gt (ha.trans_le ht.1)))).continuousWithinAt
  rcases lt_trichotomy w z with hwz | rfl | hzw
  · have hw : w ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := ⟨hw0, hwz.trans hz.2⟩
    have hanti : StrictAntiOn f (Icc w z) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc w z) (hcontinuous hw0)
      intro t ht
      rw [interior_Icc] at ht
      have htcell : t ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
        ⟨hw0.trans_le ht.1.le, ht.2.trans hz.2⟩
      exact deriv_radialTriangleDifference_div_neg_before_stationary
        halpha hr hz htcell ht.2 hstat
    exact (hanti (left_mem_Icc.2 hwz.le) (right_mem_Icc.2 hwz.le) hwz).le
  · exact le_rfl
  · have hmono : StrictMonoOn f (Icc z w) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc z w) (hcontinuous hz.1)
      intro t ht
      rw [interior_Icc] at ht
      have htcell : t ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
        ⟨hz.1.trans_le ht.1.le, ht.2.trans_le hwcap⟩
      exact deriv_radialTriangleDifference_div_pos_after_stationary
        halpha hr hz htcell ht.1 hstat
    exact (hmono (left_mem_Icc.2 hzw.le) (right_mem_Icc.2 hzw.le) hzw).le

/-- The global radial minimizer furnished by stationarity is unique. -/
theorem radialTriangleDifference_div_minimizer_unique
    {alpha : ℝ≥0} {theta r z w : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hw : w ∈ Ioc (0 : ℝ) (1 + r)⁻¹)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect (channelRho (alpha : ℝ)) r z = 0)
    (heq : radialTriangleDifference alpha theta r w / w =
      radialTriangleDifference alpha theta r z / z) :
    w = z := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hwz | hzw
  · have hwopen : w ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
      ⟨hw.1, hwz.trans hz.2⟩
    have hstrict : radialTriangleDifference alpha theta r z / z <
        radialTriangleDifference alpha theta r w / w := by
      let f : ℝ → ℝ := fun t ↦ radialTriangleDifference alpha theta r t / t
      have hanti : StrictAntiOn f (Icc w z) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc w z)
        · intro t ht
          exact ((continuous_radialTriangleDifference alpha theta r).continuousAt.div
            continuousAt_id (by simpa only [id_eq] using
              (ne_of_gt (hw.1.trans_le ht.1)))).continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          exact deriv_radialTriangleDifference_div_neg_before_stationary
            halpha hr hz ⟨by linarith [hw.1, ht.1], ht.2.trans hz.2⟩ ht.2 hstat
      exact hanti (left_mem_Icc.2 hwz.le) (right_mem_Icc.2 hwz.le) hwz
    linarith
  · have hstrict : radialTriangleDifference alpha theta r z / z <
        radialTriangleDifference alpha theta r w / w := by
      let f : ℝ → ℝ := fun t ↦ radialTriangleDifference alpha theta r t / t
      have hmono : StrictMonoOn f (Icc z w) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc z w)
        · intro t ht
          exact ((continuous_radialTriangleDifference alpha theta r).continuousAt.div
            continuousAt_id (by simpa only [id_eq] using
              (ne_of_gt (hz.1.trans_le ht.1)))).continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          exact deriv_radialTriangleDifference_div_pos_after_stationary
            halpha hr hz ⟨by linarith [hz.1, ht.1], ht.2.trans_le hw.2⟩ ht.1 hstat
      exact hmono (left_mem_Icc.2 hzw.le) (right_mem_Icc.2 hzw.le) hzw
    linarith

end CourtadeKumar
