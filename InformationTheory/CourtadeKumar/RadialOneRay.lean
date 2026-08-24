import InformationTheory.CourtadeKumar.CanonicalRadialProfile

/-! The singular shape ray `r = 1`. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Although one binary-entropy argument is identically zero on `r = 1`,
the remaining term is differentiable throughout the open ray. -/
theorem hasDerivAt_radialNatEntropy_oneRay
    {z : ℝ} (hz : 2 * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatEntropy 1 1)
      (radialNatEntropyDeriv 1 1 z) z := by
  have harg : HasDerivAt (fun w : ℝ ↦ 2 * w) 2 z := by
    simpa [id_eq] using (hasDerivAt_id z).const_mul 2
  have hentropy :=
    (Real.hasDerivAt_binEntropy hz.1.ne' hz.2.ne).comp z harg
  unfold radialNatEntropy radialNatEntropyDeriv
  convert hentropy.div_const 2 using 1 <;>
    simp [Function.comp_apply, Real.deriv_binEntropy, Real.binEntropy] <;> ring

/-- Closed Euler logarithm on the singular ray. -/
theorem radialEulerDefect_oneRay_eq_log
    {z : ℝ} (hz : 2 * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerDefect 1 1 z = radialEulerLog 1 1 z := by
  unfold radialEulerDefect radialNatEntropy radialNatEntropyDeriv
    radialEulerLog radialEulerLogArg
  simp only [one_mul, sub_self, zero_mul, Real.binEntropy_zero, zero_add,
    one_add_one_eq_two, mul_one]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_eq_neg]
  simp only [one_pow, one_mul]
  have harg : (1 - z) ^ 2 - z ^ 2 = 1 - 2 * z := by ring
  rw [harg]
  ring

theorem radialEulerRatio_eq_logRatio_oneRay
    {rho z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    radialEulerRatio rho 1 z = radialEulerLogRatio rho 1 z := by
  have hRminus : (1 - rho) * z ∈ Ioo (0 : ℝ) 1 := by
    have hcoef : 1 - rho ≤ 1 := by linarith [hrho.1]
    constructor
    · exact mul_pos (sub_pos.2 hrho.2) hz.1
    · exact (mul_le_mul_of_nonneg_right hcoef hz.1.le).trans_lt
        (by linarith [hz.2])
  have hRplus : (1 + rho) * z ∈ Ioo (0 : ℝ) 1 := by
    have hcoef : 1 + rho < 2 := by linarith [hrho.2]
    constructor
    · exact mul_pos (by linarith [hrho.1]) hz.1
    · exact (mul_lt_mul_of_pos_right hcoef hz.1).trans
        (by linarith [hz.2])
  unfold radialEulerRatio radialEulerLogRatio
  rw [radialEulerDefect_eq_logFunction (by simpa using hRminus) (by simpa using hRplus),
    radialEulerDefect_oneRay_eq_log (by constructor <;> nlinarith [hz.1, hz.2])]

theorem radialEulerDefect_oneRay_pos
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    0 < radialEulerDefect 1 1 z := by
  rw [radialEulerDefect_oneRay_eq_log (by constructor <;> nlinarith [hz.1, hz.2])]
  apply radialEulerLog_pos_of_arg
  unfold radialEulerLogArg
  constructor <;> nlinarith [hz.1, hz.2]

theorem radial_stationary_iff_ratio_oneRay
    {rho theta z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    theta * radialEulerDefect 1 1 z - radialEulerDefect rho 1 z = 0 ↔
      radialEulerLogRatio rho 1 z = theta := by
  have hD := radialEulerDefect_oneRay_pos hz
  rw [← radialEulerRatio_eq_logRatio_oneRay hrho hz]
  unfold radialEulerRatio
  constructor
  · intro h
    apply (div_eq_iff hD.ne').2
    linarith
  · intro h
    have := (div_eq_iff hD.ne').1 h
    linarith

theorem contractedEntropyArgs_oneRay
    {rho z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    (1 - rho) * z ∈ Ioo (0 : ℝ) 1 ∧
      (1 + rho) * z ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · constructor
    · exact mul_pos (sub_pos.2 hrho.2) hz.1
    · have hcoef : 1 - rho ≤ 1 := by linarith [hrho.1]
      exact (mul_le_mul_of_nonneg_right hcoef hz.1.le).trans_lt
        (by linarith [hz.2])
  · constructor
    · exact mul_pos (by linarith [hrho.1]) hz.1
    · have hcoef : 1 + rho < 2 := by linarith [hrho.2]
      exact (mul_lt_mul_of_pos_right hcoef hz.1).trans
        (by linarith [hz.2])

theorem hasDerivAt_radialNatDifference_oneRay
    {alpha : ℝ≥0} {theta z : ℝ}
    (hrho : channelRho (alpha : ℝ) ∈ Ico (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    HasDerivAt (radialNatDifference alpha theta 1)
      (radialNatEntropyDeriv (channelRho (alpha : ℝ)) 1 z -
        theta * radialNatEntropyDeriv 1 1 z) z := by
  obtain ⟨hRminus, hRplus⟩ := contractedEntropyArgs_oneRay hrho hz
  unfold radialNatDifference
  exact (hasDerivAt_radialNatEntropy (by simpa using hRminus)
    (by simpa using hRplus)).sub
      ((hasDerivAt_radialNatEntropy_oneRay
        (by constructor <;> nlinarith [hz.1, hz.2])).const_mul theta)

theorem hasDerivAt_radialTriangleDifference_div_oneRay
    {alpha : ℝ≥0} {theta z : ℝ}
    (hrho : channelRho (alpha : ℝ) ∈ Ico (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    HasDerivAt (fun w ↦ radialTriangleDifference alpha theta 1 w / w)
      ((theta * radialEulerDefect 1 1 z -
          radialEulerDefect (channelRho (alpha : ℝ)) 1 z) /
        (Real.log 2 * z ^ 2)) z := by
  have hdiff := hasDerivAt_radialNatDifference_oneRay
    (theta := theta) hrho hz
  have hquot := hdiff.div (hasDerivAt_id z) hz.1.ne'
  have hnat : HasDerivAt
      (fun w ↦ radialNatDifference alpha theta 1 w / w)
      ((theta * radialEulerDefect 1 1 z -
        radialEulerDefect (channelRho (alpha : ℝ)) 1 z) / z ^ 2) z := by
    convert hquot using 1 <;>
      simp only [id_eq] <;>
      unfold radialEulerDefect radialNatDifference <;>
      field_simp [hz.1.ne'] <;> ring
  have hscaled := hnat.div_const (Real.log 2)
  convert hscaled using 1
  · funext w
    rw [radialTriangleDifference_eq_nat]
    ring
  · field_simp [log_two_ne_zero, hz.1.ne']

theorem deriv_radialTriangleDifference_div_neg_before_stationary_oneRay
    {alpha : ℝ≥0} {theta z w : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hw : w ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hwz : w < z)
    (hstat : theta * radialEulerDefect 1 1 z -
      radialEulerDefect (channelRho (alpha : ℝ)) 1 z = 0) :
    deriv (fun t ↦ radialTriangleDifference alpha theta 1 t / t) w < 0 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrho : rho ∈ Ico (0 : ℝ) 1 :=
    channelRho_mem_Ico_of_alpha_interior halpha
  have hz' : z ∈ Ioo (0 : ℝ) (1 + (1 : ℝ))⁻¹ := by
    norm_num at hz ⊢
    exact hz
  have hw' : w ∈ Ioo (0 : ℝ) (1 + (1 : ℝ))⁻¹ := by
    norm_num at hw ⊢
    exact hw
  have hratioZ : radialEulerLogRatio rho 1 z = theta :=
    (radial_stationary_iff_ratio_oneRay hrho hz).1 hstat
  have hlogRatio : theta < radialEulerLogRatio rho 1 w := by
    rw [← hratioZ]
    exact (radialEulerLogRatio_strictAntiOn_physical hrho (by norm_num)) hw' hz' hwz
  have hratio : theta < radialEulerRatio rho 1 w := by
    rw [radialEulerRatio_eq_logRatio_oneRay hrho hw]
    exact hlogRatio
  have hD := radialEulerDefect_oneRay_pos hw
  have hnum : theta * radialEulerDefect 1 1 w -
      radialEulerDefect rho 1 w < 0 := by
    unfold radialEulerRatio at hratio
    have := (lt_div_iff₀ hD).1 hratio
    linarith
  rw [(hasDerivAt_radialTriangleDifference_div_oneRay hrho hw).deriv]
  exact div_neg_of_neg_of_pos hnum
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hw.1))

theorem deriv_radialTriangleDifference_div_pos_after_stationary_oneRay
    {alpha : ℝ≥0} {theta z w : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hw : w ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hzw : z < w)
    (hstat : theta * radialEulerDefect 1 1 z -
      radialEulerDefect (channelRho (alpha : ℝ)) 1 z = 0) :
    0 < deriv (fun t ↦ radialTriangleDifference alpha theta 1 t / t) w := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrho : rho ∈ Ico (0 : ℝ) 1 :=
    channelRho_mem_Ico_of_alpha_interior halpha
  have hz' : z ∈ Ioo (0 : ℝ) (1 + (1 : ℝ))⁻¹ := by
    norm_num at hz ⊢
    exact hz
  have hw' : w ∈ Ioo (0 : ℝ) (1 + (1 : ℝ))⁻¹ := by
    norm_num at hw ⊢
    exact hw
  have hratioZ : radialEulerLogRatio rho 1 z = theta :=
    (radial_stationary_iff_ratio_oneRay hrho hz).1 hstat
  have hlogRatio : radialEulerLogRatio rho 1 w < theta := by
    rw [← hratioZ]
    exact (radialEulerLogRatio_strictAntiOn_physical hrho (by norm_num)) hz' hw' hzw
  have hratio : radialEulerRatio rho 1 w < theta := by
    rw [radialEulerRatio_eq_logRatio_oneRay hrho hw]
    exact hlogRatio
  have hD := radialEulerDefect_oneRay_pos hw
  have hnum : 0 < theta * radialEulerDefect 1 1 w -
      radialEulerDefect rho 1 w := by
    unfold radialEulerRatio at hratio
    have := (div_lt_iff₀ hD).1 hratio
    linarith
  rw [(hasDerivAt_radialTriangleDifference_div_oneRay hrho hw).deriv]
  exact div_pos hnum
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hw.1))

/-- The singular-ray stationary contact is still the global radial
perspective minimum, including the endpoint `z = 1/2`. -/
theorem radialTriangleDifference_div_min_oneRay_of_stationary
    {alpha : ℝ≥0} {theta z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hstat : theta * radialEulerDefect 1 1 z -
      radialEulerDefect (channelRho (alpha : ℝ)) 1 z = 0) :
    ∀ w : ℝ, 0 < w → w ≤ 1 / 2 →
      radialTriangleDifference alpha theta 1 z / z ≤
        radialTriangleDifference alpha theta 1 w / w := by
  intro w hw0 hwcap
  let f : ℝ → ℝ := fun t ↦ radialTriangleDifference alpha theta 1 t / t
  have hcontinuous : ∀ {a b : ℝ}, 0 < a → ContinuousOn f (Icc a b) := by
    intro a b ha t ht
    exact ((continuous_radialTriangleDifference alpha theta 1).continuousAt.div
      continuousAt_id (by simpa only [id_eq] using
        (ne_of_gt (ha.trans_le ht.1)))).continuousWithinAt
  rcases lt_trichotomy w z with hwz | rfl | hzw
  · have hw : w ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := ⟨hw0, hwz.trans hz.2⟩
    have hanti : StrictAntiOn f (Icc w z) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc w z) (hcontinuous hw0)
      intro t ht
      rw [interior_Icc] at ht
      exact deriv_radialTriangleDifference_div_neg_before_stationary_oneRay
        halpha hz ⟨hw0.trans_le ht.1.le, ht.2.trans hz.2⟩ ht.2 hstat
    exact (hanti (left_mem_Icc.2 hwz.le) (right_mem_Icc.2 hwz.le) hwz).le
  · exact le_rfl
  · have hmono : StrictMonoOn f (Icc z w) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc z w) (hcontinuous hz.1)
      intro t ht
      rw [interior_Icc] at ht
      exact deriv_radialTriangleDifference_div_pos_after_stationary_oneRay
        halpha hz ⟨hz.1.trans_le ht.1.le, ht.2.trans_le hwcap⟩ ht.1 hstat
    exact (hmono (left_mem_Icc.2 hzw.le) (right_mem_Icc.2 hzw.le) hzw).le

/-- The canonical profile supplies the singular-ray contact automatically. -/
theorem canonicalRadialProfile_oneRayContact
    {alpha : ℝ≥0} {theta : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    RadialOneRayContact alpha theta
      (canonicalRadialProfile alpha theta halpha htheta) := by
  let z : ℝ := canonicalRadialContactZ alpha theta halpha htheta 1
  have hzspec := canonicalRadialContactZ_spec halpha htheta (by norm_num : (0 : ℝ) < 1)
  have hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := by
    dsimp [z]
    norm_num at hzspec ⊢
    exact hzspec.1
  have hrho := channelRho_mem_Ico_of_alpha_interior halpha
  have hstat : theta * radialEulerDefect 1 1 z -
      radialEulerDefect (channelRho (alpha : ℝ)) 1 z = 0 :=
    (radial_stationary_iff_ratio_oneRay hrho hz).2 hzspec.2
  refine ⟨z, hz.1, hz.2.le, ?_, ?_⟩
  · dsimp [z]
    simp [canonicalRadialProfile]
  · intro w hw0 hwcap
    dsimp [z] at hstat ⊢
    rw [show canonicalRadialProfile alpha theta halpha htheta 1 =
        radialTriangleDifference alpha theta 1
          (canonicalRadialContactZ alpha theta halpha htheta 1) /
            canonicalRadialContactZ alpha theta halpha htheta 1 by
      simp [canonicalRadialProfile]]
    exact radialTriangleDifference_div_min_oneRay_of_stationary
      halpha hz hstat w hw0 hwcap

/-- Thus the canonical Euler-root construction is a fully attained radial
profile on the entire closed shape interval. -/
theorem canonicalRadialProfile_contactProfile
    {alpha : ℝ≥0} {theta : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    RadialContactProfile alpha theta
      (canonicalRadialProfile alpha theta halpha htheta) :=
  radialContactProfile_of_stationaryRoots halpha htheta.2.le
    (canonicalRadialProfile_zero alpha theta halpha htheta)
    (canonicalRadialProfile_interiorStationary halpha htheta)
    (canonicalRadialProfile_oneRayContact halpha htheta)

end CourtadeKumar
