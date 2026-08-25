import InformationTheory.CourtadeKumar.CanonicalRadialProfile
import InformationTheory.CourtadeKumar.RadialEntropyRatio

/-! The singular shape ray `r = 1`. -/

open Filter Set
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

/-- Entropy per unit mass remains differentiable on the singular ray even
though the vanished entropy summand is not differentiable by itself. -/
theorem hasDerivAt_radialEntropyRatio_oneRay
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    HasDerivAt (radialEntropyRatio 1)
      (-radialEulerDefect 1 1 z / (Real.log 2 * z ^ 2)) z := by
  have hnat := hasDerivAt_radialNatEntropy_oneRay (z := z)
    (by constructor <;> nlinarith [hz.1, hz.2])
  have hquot := hnat.div (hasDerivAt_id z) hz.1.ne'
  have hscaled := hquot.div_const (Real.log 2)
  convert hscaled using 1
  · funext w
    rw [radialEntropyRatio, radialTriangleEntropy_eq_nat]
    change radialNatEntropy 1 1 w / Real.log 2 / w =
      (radialNatEntropy 1 1 w / w) / Real.log 2
    ring
  · unfold radialEulerDefect
    simp only [id_eq, mul_one]
    field_simp [hz.1.ne', log_two_ne_zero]
    ring

theorem deriv_radialEntropyRatio_oneRay_neg
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    deriv (radialEntropyRatio 1) z < 0 := by
  rw [(hasDerivAt_radialEntropyRatio_oneRay hz).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (radialEulerDefect_oneRay_pos hz))
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hz.1))

/-- On `r = 1`, entropy per unit mass decreases strictly from the zero-mass
limit up to the hard endpoint. -/
theorem strictAntiOn_radialEntropyRatio_oneRay :
    StrictAntiOn (radialEntropyRatio 1) (Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) (1 / 2))
  · intro z hz
    exact (hasDerivAt_radialEntropyRatio_oneRay hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    exact deriv_radialEntropyRatio_oneRay_neg hz

lemma radialEntropyRatio_oneRay_eq (z : ℝ) :
    radialEntropyRatio 1 z = binaryEntropyBits (2 * z) / (2 * z) := by
  unfold radialEntropyRatio radialTriangleEntropy
  simp [binaryEntropyBits, Real.binEntropy]
  ring

theorem tendsto_radialEntropyRatio_oneRay_zero :
    Tendsto (radialEntropyRatio 1)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  rw [show radialEntropyRatio 1 =
      fun z : ℝ ↦ binaryEntropyBits (2 * z) / (2 * z) by
    funext z
    exact radialEntropyRatio_oneRay_eq z]
  exact tendsto_binaryEntropyBits_scaled_div_zero (by norm_num)

/-- Every positive entropy-per-mass level has a unique singular-ray contact
strictly before `1/2`. -/
theorem existsUnique_radialEntropyRatio_oneRay_eq_before_half
    {t : ℝ} (ht : 0 < t) :
    ∃! z : ℝ, z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) ∧
      radialEntropyRatio 1 z = t := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have hlarge : ∀ᶠ z in l, t < radialEntropyRatio 1 z :=
    tendsto_radialEntropyRatio_oneRay_zero.eventually (eventually_gt_atTop t)
  have hsmall : ∀ᶠ z in l, z < (1 / 2 : ℝ) :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      nhdsWithin_le_nhds
  have hpositive : ∀ᶠ z in l, 0 < z := self_mem_nhdsWithin
  obtain ⟨a, ha0, hahalf, hat⟩ :=
    (hpositive.and (hsmall.and hlarge)).exists
  have hcont : ContinuousOn (radialEntropyRatio 1) (Icc a (1 / 2)) := by
    intro z hz
    rcases hz.2.eq_or_lt with rfl | hzhalf
    · rw [show radialEntropyRatio 1 =
          fun w : ℝ ↦ binaryEntropyBits (2 * w) / (2 * w) by
        funext w
        exact radialEntropyRatio_oneRay_eq w]
      have hnum : ContinuousAt
          (fun w : ℝ ↦ binaryEntropyBits (2 * w)) (1 / 2) := by
        unfold binaryEntropyBits
        fun_prop
      have hden : ContinuousAt (fun w : ℝ ↦ 2 * w) (1 / 2) := by
        fun_prop
      exact (hnum.div hden (by norm_num)).continuousWithinAt
    · exact (hasDerivAt_radialEntropyRatio_oneRay
        ⟨ha0.trans_le hz.1, hzhalf⟩).continuousAt.continuousWithinAt
  have hhalf : radialEntropyRatio 1 (1 / 2) = 0 := by
    rw [radialEntropyRatio_oneRay_eq]
    simp [binaryEntropyBits, Real.binEntropy]
  have htmem : t ∈ Icc (radialEntropyRatio 1 (1 / 2))
      (radialEntropyRatio 1 a) := by
    rw [hhalf]
    exact ⟨ht.le, hat.le⟩
  obtain ⟨z, hzrange, hzeq⟩ :=
    intermediate_value_Icc' hahalf.le hcont htmem
  have hz0 : 0 < z := ha0.trans_le hzrange.1
  have hzhalf : z < 1 / 2 := by
    rcases hzrange.2.eq_or_lt with h | h
    · rw [h, hhalf] at hzeq
      linarith
    · exact h
  refine ⟨z, ⟨⟨hz0, hzhalf⟩, hzeq⟩, ?_⟩
  intro w hw
  exact strictAntiOn_radialEntropyRatio_oneRay.injOn
    hw.1 ⟨hz0, hzhalf⟩ (hw.2.trans hzeq.symm)

/-- A genuine contact on the singular ray still selects an interior entropy
multiplier. -/
theorem radialEulerLogRatio_mem_Ioo_oneRay
    {rho z : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    radialEulerLogRatio rho 1 z ∈ Ioo (0 : ℝ) 1 := by
  have hupper : (1 + (1 : ℝ)) * z < 1 := by linarith [hz.2]
  obtain ⟨harg1, hargR, horder⟩ :=
    radialEulerLogArg_order_physical
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
      (by norm_num) hz.1 hupper
  have harg1' : radialEulerLogArg 1 1 z ∈ Ioo (0 : ℝ) 1 :=
    ⟨harg1.1, harg1.2.trans (by linarith [hz.1])⟩
  have hargR' : radialEulerLogArg rho 1 z ∈ Ioo (0 : ℝ) 1 :=
    ⟨hargR.1, hargR.2.trans (by linarith [hz.1])⟩
  have hden : 0 < radialEulerLog 1 1 z :=
    radialEulerLog_pos_of_arg harg1'
  have hnum : 0 < radialEulerLog rho 1 z :=
    radialEulerLog_pos_of_arg hargR'
  have hlogOrder : Real.log (radialEulerLogArg 1 1 z) <
      Real.log (radialEulerLogArg rho 1 z) :=
    Real.log_lt_log harg1.1 horder
  have hnumden : radialEulerLog rho 1 z < radialEulerLog 1 1 z := by
    unfold radialEulerLog
    nlinarith
  unfold radialEulerLogRatio
  exact ⟨div_pos hnum hden, (div_lt_one hden).2 hnumden⟩

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
