import InformationTheory.CourtadeKumar.ArtanhDerivative
import Mathlib.Analysis.Convex.Deriv

/-! Positivity of the corrected TOP energy and equal-multiplier coefficient. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- `artanh` is convex on the nonnegative part of its finite domain. -/
theorem artanh_convexOn_Ico : ConvexOn ℝ (Ico (0 : ℝ) 1) Real.artanh := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ico 0 1)
  · intro x hx
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_artanh hx').continuousAt.continuousWithinAt
  · rw [interior_Ico]
    intro x hx
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_artanh hx').differentiableAt.differentiableWithinAt
  · rw [interior_Ico]
    intro x hx y hy hxy
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
    rw [(hasDerivAt_artanh hx').deriv, (hasDerivAt_artanh hy').deriv]
    have hdenx : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hdeny : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    apply one_div_le_one_div_of_le hdeny
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx.1.le hy.1.le)]

/-- The contraction inequality for `artanh` on `[0,1)`. -/
lemma artanh_mul_le_mul_artanh {a x : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : x ∈ Ico (0 : ℝ) 1) :
    Real.artanh (a * x) ≤ a * Real.artanh x := by
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  have hcombo := artanh_convexOn_Ico.2 hzero hx (sub_nonneg.mpr ha.2) ha.1
    (by linarith [ha.1, ha.2])
  simpa [Real.artanh_zero] using hcombo

lemma continuous_topPhi : Continuous topPhi := by
  unfold topPhi
  fun_prop

/-- For a fixed channel, the contraction remainder increases with the ray
parameter. -/
theorem topEnergy_monotoneOn_nonneg {rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (topEnergy rho) (Icc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · unfold topEnergy
    exact (continuous_const.mul continuous_topPhi).sub
      (continuous_topPhi.comp (continuous_const.mul continuous_id)) |>.continuousOn
  · rw [interior_Icc]
    intro z hz
    have hz' : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
    have hrhoz : rho * z ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [hrho.1, hz.1]
      · nlinarith [hrho.1, hrho.2, hz.1, hz.2]
    have hleft := (hasDerivAt_topPhi hz').const_mul (rho ^ 2)
    have harg : HasDerivAt (fun y : ℝ ↦ rho * y) rho z := by
      simpa [mul_comm] using (hasDerivAt_id z).const_mul rho
    have hright := (hasDerivAt_topPhi hrhoz).comp z harg
    exact (hleft.sub hright).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    have hz' : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
    have hrhoz : rho * z ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [hrho.1, hz.1]
      · nlinarith [hrho.1, hrho.2, hz.1, hz.2]
    have hleft := (hasDerivAt_topPhi hz').const_mul (rho ^ 2)
    have harg : HasDerivAt (fun y : ℝ ↦ rho * y) rho z := by
      simpa [mul_comm] using (hasDerivAt_id z).const_mul rho
    have hright := (hasDerivAt_topPhi hrhoz).comp z harg
    have htotal : HasDerivAt (topEnergy rho)
        (rho ^ 2 * Real.artanh z - Real.artanh (rho * z) * rho) z := by
      simpa only [topEnergy] using hleft.sub hright
    rw [htotal.deriv]
    have hartanh := artanh_mul_le_mul_artanh hrho ⟨hz.1.le, hz.2⟩
    nlinarith [mul_nonneg hrho.1 (sub_nonneg.mpr hartanh)]

/-- Positivity of the corrected TOP contraction remainder. -/
theorem topEnergy_nonneg {rho z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ topEnergy rho z := by
  have hmono := topEnergy_monotoneOn_nonneg hrho
  have h := hmono (show (0 : ℝ) ∈ Icc 0 1 by simp) hz hz.1
  simpa [topEnergy] using h

/-- The equal-multiplier coefficient is nonnegative for every BSC channel. -/
theorem topEll_nonneg {rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) :
    0 ≤ topEll rho := by
  rw [show topEll rho = topEnergy rho 1 by simp [topEll, topEnergy, topR]]
  exact topEnergy_nonneg hrho (show (1 : ℝ) ∈ Icc 0 1 by simp)

lemma topS_nonneg {rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) :
    0 ≤ topS rho := by
  unfold topS topR
  nlinarith [sq_nonneg rho, mul_nonneg (sub_nonneg.mpr hrho.2) (add_nonneg hrho.1 zero_le_one)]

/-- The TOP slope is monotone for every admissible channel, with the
coefficient signs now discharged internally. -/
theorem topP_monotoneOn_channel {rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (topP rho) (Ioo (-1 : ℝ) 1) :=
  topP_monotoneOn rho (topS_nonneg hrho) (topEll_nonneg hrho)

/-- A fixed-weight contact brackets the centered and transition residuals
for every admissible channel. -/
theorem topContactResidual_bracket_of_contact_channel
    {rho c r X U : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    topContactResidual rho c r 0 ≤ 0 ∧
      0 ≤ topContactResidual rho c r U :=
  topContactResidual_bracket_of_contact (topS_nonneg hrho) (topEll_nonneg hrho)
    hX hdomain hcontact

theorem balancedResidual_nonpos_of_contact_channel
    {rho c r X U : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    balancedResidual rho c r ≤ 0 :=
  balancedResidual_nonpos_of_contact (topS_nonneg hrho) (topEll_nonneg hrho)
    hX hdomain hcontact

/-- Consequently the bit-valued Bellman coefficient is nonnegative on the
whole BSC parameter interval. -/
theorem bellmanLambda_nonneg {alpha : ℝ}
    (halpha : alpha ∈ Icc (0 : ℝ) (1 / 2 : ℝ)) :
    0 ≤ bellmanLambda alpha := by
  have hrho : channelRho alpha ∈ Icc (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have h := topEll_nonneg hrho
  rw [topEll_channelRho] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Concavity of the explicit Bellman envelope now has no auxiliary sign
hypothesis. -/
theorem bellmanEnvelope_concaveOn
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (bellmanEnvelope (alpha : ℝ)) := by
  have ha1 : alpha ≤ 1 := by
    exact_mod_cast (show (alpha : ℝ) ≤ 1 by linarith)
  exact bellmanEnvelope_concaveOn_of_lambda_nonneg alpha ha1
    (bellmanLambda_nonneg ⟨alpha.2, halpha⟩)

/-- The sorting reduction required by Boolean induction is therefore
available for every admissible BSC channel. -/
theorem bellmanEnvelopeSortingDominance
    (alpha : ℝ≥0) (halpha : (alpha : ℝ) ≤ 1 / 2) :
    BellmanEnvelopeSortingDominance alpha := by
  have ha1 : alpha ≤ 1 := by
    exact_mod_cast (show (alpha : ℝ) ≤ 1 by linarith)
  exact bellmanEnvelopeSortingDominance_of_lambda_nonneg alpha ha1
    (bellmanLambda_nonneg ⟨alpha.2, halpha⟩)

end CourtadeKumar
