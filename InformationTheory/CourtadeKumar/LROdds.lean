import InformationTheory.CourtadeKumar.PerspectiveFullWidth
import InformationTheory.CourtadeKumar.TopNormalizedReserve
import InformationTheory.CourtadeKumar.SingleRayContactAlgebra

/-! The exact odds-coordinate dictionary and automatic/root split in the
audited LR proof. -/

open Set
open scoped NNReal

namespace CourtadeKumar

noncomputable def lrOddsToProbability (q : ℝ) : ℝ := q / (1 + q)

noncomputable def lrL (z : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - z ^ 2)

noncomputable def lrG (q : ℝ) : ℝ :=
  (1 + 1 / q) * Real.log (1 + q) - Real.log q

noncomputable def lrGShape (t q : ℝ) : ℝ :=
  lrG q - topPhi t - topPhi (q * t) / q

noncomputable def lrMu (rho : ℝ) : ℝ :=
  4 * topEnergy rho 1 / topS rho

noncomputable def lrEntropyTarget (rho u t : ℝ) : ℝ :=
  topS rho *
    (lrGShape t u + lrMu rho * (1 - u * t ^ 2) / (1 + u))

noncomputable def lrObjectiveTarget (rho u : ℝ) : ℝ :=
  topS rho * (lrG u + lrMu rho / (1 + u))

lemma lrOddsToProbability_pos {q : ℝ} (hq : 0 < q) :
    0 < lrOddsToProbability q := by
  unfold lrOddsToProbability
  positivity

lemma lrOddsToProbability_lt_one {q : ℝ} (hq : 0 < q) :
    lrOddsToProbability q < 1 := by
  unfold lrOddsToProbability
  rw [div_lt_one (by linarith)]
  linarith

lemma one_sub_lrOddsToProbability {q : ℝ} (hq : q ≠ -1) :
    1 - lrOddsToProbability q = 1 / (1 + q) := by
  unfold lrOddsToProbability
  have hden : 1 + q ≠ 0 := by
    intro h
    apply hq
    linarith
  field_simp [hden]
  ring

lemma lrG_eq_binEntropy_div {q : ℝ} (hq : 0 < q) :
    lrG q = Real.binEntropy (lrOddsToProbability q) /
      lrOddsToProbability q := by
  have hqp : 0 < 1 + q := by linarith
  have hq1 : q ≠ -1 := by linarith
  unfold lrG
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    one_sub_lrOddsToProbability hq1]
  simp only [Real.negMulLog_eq_neg]
  change (1 + 1 / q) * Real.log (1 + q) - Real.log q =
    (-(lrOddsToProbability q * Real.log (lrOddsToProbability q)) +
      -(1 / (1 + q) * Real.log (1 / (1 + q)))) /
        lrOddsToProbability q
  rw [show lrOddsToProbability q = q / (1 + q) by rfl,
    Real.log_div hq.ne' hqp.ne', Real.log_div one_ne_zero hqp.ne',
    Real.log_one]
  field_simp [hq.ne', hqp.ne']
  ring

lemma binEntropy_mul_odds_formula
    {q a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hcomp : 0 < 1 + q - a * q) :
    Real.binEntropy (a * q / (1 + q)) =
      -(a * q / (1 + q)) *
          (Real.log a + Real.log q - Real.log (1 + q)) -
        ((1 + q - a * q) / (1 + q)) *
          (Real.log (1 + q - a * q) - Real.log (1 + q)) := by
  have hden : 0 < 1 + q := by linarith
  have honeSub : 1 - a * q / (1 + q) =
      (1 + q - a * q) / (1 + q) := by
    field_simp [hden.ne']
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, honeSub]
  simp only [Real.negMulLog_eq_neg]
  rw [Real.log_div (mul_pos ha hq).ne' hden.ne',
    Real.log_mul ha.ne' hq.ne', Real.log_div hcomp.ne' hden.ne']
  ring

theorem lrGShape_eq_radialNatEntropy_div
    {t q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    lrGShape t q =
      radialNatEntropy 1 t (lrOddsToProbability q) /
        lrOddsToProbability q := by
  have hden : 0 < 1 + q := by linarith
  have htPlus : 0 < 1 + t := by linarith
  have htMinus : 0 < 1 - t := by linarith
  have hqt0 : 0 ≤ q * t := mul_nonneg hq.le ht0
  have hqt1 : q * t < 1 := by
    calc
      q * t ≤ 1 * t := mul_le_mul_of_nonneg_right hq1 ht0
      _ < 1 := by simpa using ht1
  have hqtPlus : 0 < 1 + q * t := by linarith
  have hqtMinus : 0 < 1 - q * t := by linarith
  have hcompMinus : 0 < 1 + q - (1 - t) * q := by nlinarith
  have hcompPlus : 0 < 1 + q - (1 + t) * q := by nlinarith
  have htIoo : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have hqtIoo : q * t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hqt1⟩
  have hminus := binEntropy_mul_odds_formula hq htMinus hcompMinus
  have hplus := binEntropy_mul_odds_formula hq htPlus hcompPlus
  rw [lrGShape, lrG, topPhi_eq_log_formula htIoo,
    topPhi_eq_log_formula hqtIoo]
  unfold radialNatEntropy lrOddsToProbability
  rw [show (1 - 1 * t) * (q / (1 + q)) = (1 - t) * q / (1 + q) by ring,
    show (1 + 1 * t) * (q / (1 + q)) = (1 + t) * q / (1 + q) by ring,
    hminus, hplus]
  rw [show 1 + q - (1 - t) * q = 1 + q * t by ring,
    show 1 + q - (1 + t) * q = 1 - q * t by ring]
  field_simp [hq.ne', hden.ne']
  ring

theorem lr_probability_odds_entropy
    {t q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log 2 * radialTriangleEntropy t (lrOddsToProbability q) /
        lrOddsToProbability q = lrGShape t q := by
  rw [radialTriangleEntropy_eq_nat]
  have h := lrGShape_eq_radialNatEntropy_div hq hq1 ht0 ht1
  rw [h]
  field_simp [log_two_ne_zero]

lemma radialNatEntropy_contract_shape (rho t z : ℝ) :
    radialNatEntropy rho t z = radialNatEntropy 1 (rho * t) z := by
  unfold radialNatEntropy
  ring

theorem lr_probability_odds_channelEntropy
    {alpha : ℝ≥0} {t q : ℝ}
    (halpha : (alpha : ℝ) ∈ Icc (0 : ℝ) (1 / 2 : ℝ))
    (hq : 0 < q) (hq1 : q ≤ 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log 2 *
        radialTriangleChannelEntropy alpha t (lrOddsToProbability q) /
          lrOddsToProbability q =
      lrGShape (channelRho (alpha : ℝ) * t) q := by
  rw [radialTriangleChannelEntropy_eq_nat,
    radialNatEntropy_contract_shape]
  have hrho : channelRho (alpha : ℝ) ∈ Icc (0 : ℝ) 1 := by
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hshape0 : 0 ≤ channelRho (alpha : ℝ) * t :=
    mul_nonneg hrho.1 ht0
  have hshape1 : channelRho (alpha : ℝ) * t < 1 := by
    calc
      channelRho (alpha : ℝ) * t ≤ 1 * t :=
        mul_le_mul_of_nonneg_right hrho.2 ht0
      _ < 1 := by simpa using ht1
  have h := lrGShape_eq_radialNatEntropy_div hq hq1 hshape0 hshape1
  rw [h]
  field_simp [log_two_ne_zero]

lemma mul_artanh_sub_topPhi_eq_lrL
    {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    z * Real.artanh z - topPhi z = lrL z := by
  rw [topPhi_eq_mul_artanh_add_log hz]
  unfold lrL
  ring

theorem hasDerivAt_lrG {q : ℝ} (hq : 0 < q) :
    HasDerivAt lrG (-Real.log (1 + q) / q ^ 2) q := by
  have hq0 : q ≠ 0 := hq.ne'
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 q := by
    convert (hasDerivAt_const q 1).add (hasDerivAt_id q) using 1 <;> ring
  have hlogPlus := hplus.log (by linarith : 1 + q ≠ 0)
  have hcoef : HasDerivAt (fun x : ℝ ↦ 1 + 1 / x) (-1 / q ^ 2) q := by
    convert (hasDerivAt_const q 1).add
      ((hasDerivAt_const q 1).div (hasDerivAt_id q) hq0) using 1 <;>
      simp only [id_eq] <;> field_simp [hq0] <;> ring
  have hlogQ := (hasDerivAt_id q).log hq0
  have h := (hcoef.mul hlogPlus).sub hlogQ
  convert h using 1 <;> simp only [id_eq] <;>
    field_simp [hq0] <;> ring

theorem hasDerivAt_lrGShape
    {a q : ℝ} (hq : 0 < q) (ha0 : 0 ≤ a) (haq : a * q < 1) :
    HasDerivAt (lrGShape a)
      (-(Real.log (1 + q) + lrL (a * q)) / q ^ 2) q := by
  have hq0 : q ≠ 0 := hq.ne'
  have haqIoo : a * q ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) (mul_nonneg ha0 hq.le)
    · exact haq
  have harg : HasDerivAt (fun x : ℝ ↦ a * x) a q := by
    simpa using (hasDerivAt_id q).const_mul a
  have hphi := (hasDerivAt_topPhi haqIoo).comp q harg
  have hquot := hphi.div (hasDerivAt_id q) hq0
  have h := ((hasDerivAt_lrG hq).sub_const (topPhi a)).sub hquot
  convert h using 1
  · funext x
    simp [lrGShape, Function.comp_apply, mul_comm]
  · simp only [id_eq, Function.comp_apply]
    rw [← mul_artanh_sub_topPhi_eq_lrL haqIoo]
    field_simp [hq0]
    ring

lemma lrL_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ lrL z := by
  have harg0 : 0 ≤ 1 - z ^ 2 := by nlinarith
  have harg1 : 1 - z ^ 2 ≤ 1 := by nlinarith
  have hlog := Real.log_nonpos harg0 harg1
  unfold lrL
  nlinarith

theorem deriv_lrGShape_neg
    {a q : ℝ} (hq : 0 < q) (ha0 : 0 ≤ a) (haq : a * q < 1) :
    deriv (lrGShape a) q < 0 := by
  rw [(hasDerivAt_lrGShape hq ha0 haq).deriv]
  have hlog : 0 < Real.log (1 + q) := Real.log_pos (by linarith)
  have hL : 0 ≤ lrL (a * q) :=
    lrL_nonneg (mul_nonneg ha0 hq.le) haq
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (add_pos_of_pos_of_nonneg hlog hL)) (sq_pos_of_pos hq)

/-- This is equation `G_a'(q)<0` in the manuscript. -/
theorem strictAntiOn_lrGShape
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (lrGShape a) (Ioo (0 : ℝ) a⁻¹) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) a⁻¹)
  · intro q hq
    have haq : a * q < 1 := by
      have hdiv : q < 1 / a := by simpa [one_div] using hq.2
      have hmul : q * a < 1 := (lt_div_iff₀ ha.1).mp hdiv
      simpa [mul_comm] using hmul
    exact (hasDerivAt_lrGShape hq.1 ha.1.le haq).continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ioo] at hq
    have haq : a * q < 1 := by
      have hdiv : q < 1 / a := by simpa [one_div] using hq.2
      have hmul : q * a < 1 := (lt_div_iff₀ ha.1).mp hdiv
      simpa [mul_comm] using hmul
    exact deriv_lrGShape_neg hq.1 ha.1.le haq

/-- The root branch of the manuscript's automatic/root split. -/
theorem existsUnique_lrGShape_eq_of_bracket
    {a u target : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hupper : lrGShape a 1 ≤ target)
    (hlower : target ≤ lrGShape a u) :
    ∃! v : ℝ, v ∈ Icc u 1 ∧ lrGShape a v = target := by
  have honeCap : (1 : ℝ) < a⁻¹ := by
    rw [one_lt_inv₀ ha.1]
    exact ha.2
  have hcont : ContinuousOn (lrGShape a) (Icc u 1) := by
    intro q hq
    have hq0 : 0 < q := hu.1.trans_le hq.1
    have haq : a * q < 1 := by
      calc
        a * q ≤ a * 1 := mul_le_mul_of_nonneg_left hq.2 ha.1.le
        _ < 1 := by simpa using ha.2
    exact (hasDerivAt_lrGShape hq0 ha.1.le haq).continuousAt.continuousWithinAt
  obtain ⟨v, hv, hvalue⟩ :=
    intermediate_value_Icc' hu.2.le hcont ⟨hupper, hlower⟩
  refine ⟨v, ⟨hv, hvalue⟩, ?_⟩
  intro w hw
  have hvDomain : v ∈ Ioo (0 : ℝ) a⁻¹ :=
    ⟨hu.1.trans_le hv.1, hv.2.trans_lt honeCap⟩
  have hwDomain : w ∈ Ioo (0 : ℝ) a⁻¹ :=
    ⟨hu.1.trans_le hw.1.1, hw.1.2.trans_lt honeCap⟩
  exact (strictAntiOn_lrGShape ha).injOn hwDomain hvDomain
    (hw.2.trans hvalue.symm)

lemma topEnergy_one (rho : ℝ) : topEnergy rho 1 = topEll rho := by
  simp [topEnergy, topEll, topR]

/-- Equation (lr-entropy-contact): the manuscript's odds contact is exactly
the natural-unit radial contact already used by the perspective reduction. -/
theorem singleRayNatContact_iff_lrEntropyContact
    {rho u v t : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    let M := lrOddsToProbability u
    let z := lrOddsToProbability v
    M / z * radialNatEntropy 1 t z =
        (lowerRayNatEnvelope rho (M * (1 - t)) +
          lowerRayNatEnvelope rho (M * (1 + t))) / 2 ↔
      lrGShape t v = lrEntropyTarget rho u t := by
  dsimp only
  have huDen : 0 < 1 + u := by linarith [hu.1]
  have hM : 0 < lrOddsToProbability u := lrOddsToProbability_pos hu.1
  have hz : 0 < lrOddsToProbability v := lrOddsToProbability_pos hv.1
  have hs : topS rho ≠ 0 := by
    unfold topS topR
    nlinarith [hrho.1, hrho.2]
  have hGu := lrGShape_eq_radialNatEntropy_div hu.1 hu.2.le ht.1.le ht.2
  have hGv := lrGShape_eq_radialNatEntropy_div hv.1 hv.2 ht.1.le ht.2
  rw [average_lowerRayNatEnvelope_radial]
  have hleft :
      lrOddsToProbability u / lrOddsToProbability v *
          radialNatEntropy 1 t (lrOddsToProbability v) =
        lrOddsToProbability u * lrGShape t v := by
    rw [hGv]
    field_simp [hz.ne']
  have hentropyM :
      radialNatEntropy 1 t (lrOddsToProbability u) =
        lrOddsToProbability u * lrGShape t u := by
    rw [hGu]
    field_simp [hM.ne']
  have hright :
      topS rho * radialNatEntropy 1 t (lrOddsToProbability u) +
          4 * topEll rho * lrOddsToProbability u *
            (1 - lrOddsToProbability u * (1 + t ^ 2)) =
        lrOddsToProbability u * lrEntropyTarget rho u t := by
    rw [hentropyM]
    rw [show topEll rho = topEnergy rho 1 by rw [topEnergy_one]]
    unfold lrEntropyTarget lrMu lrOddsToProbability
    field_simp [hu.1.ne', huDen.ne', hs]
    ring
  rw [hleft, hright]
  constructor <;> intro h
  · exact mul_left_cancel₀ hM.ne' h
  · exact congrArg (fun x : ℝ ↦ lrOddsToProbability u * x) h

/-- Equation (lr-target): the LR objective is exactly the target comparison
in odds coordinates. -/
theorem singleRayNatLR_iff_lrObjectiveTarget
    {rho u v t : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    let M := lrOddsToProbability u
    let z := lrOddsToProbability v
    lowerRayNatEnvelope rho M ≤ M / z * radialNatEntropy rho t z ↔
      lrObjectiveTarget rho u ≤ lrGShape (rho * t) v := by
  dsimp only
  have huDen : 0 < 1 + u := by linarith [hu.1]
  have hM : 0 < lrOddsToProbability u := lrOddsToProbability_pos hu.1
  have hz : 0 < lrOddsToProbability v := lrOddsToProbability_pos hv.1
  have hs : topS rho ≠ 0 := by
    unfold topS topR
    nlinarith [hrho.1, hrho.2]
  have hshape0 : 0 ≤ rho * t := mul_nonneg hrho.1.le ht.1.le
  have hshape1 : rho * t < 1 := by
    calc
      rho * t ≤ 1 * t := mul_le_mul_of_nonneg_right hrho.2.le ht.1.le
      _ < 1 := by simpa using ht.2
  have hGout := lrGShape_eq_radialNatEntropy_div
    hv.1 hv.2 hshape0 hshape1
  rw [← radialNatEntropy_contract_shape] at hGout
  have hGinput := lrG_eq_binEntropy_div hu.1
  have hleft :
      lowerRayNatEnvelope rho (lrOddsToProbability u) =
        lrOddsToProbability u * lrObjectiveTarget rho u := by
    unfold lowerRayNatEnvelope lrObjectiveTarget lrMu
    rw [hGinput]
    rw [show topEll rho = topEnergy rho 1 by rw [topEnergy_one]]
    unfold lrOddsToProbability
    field_simp [hu.1.ne', huDen.ne', hs]
    ring
  have hright :
      lrOddsToProbability u / lrOddsToProbability v *
          radialNatEntropy rho t (lrOddsToProbability v) =
        lrOddsToProbability u * lrGShape (rho * t) v := by
    rw [hGout]
    field_simp [hz.ne']
  rw [hleft, hright]
  constructor <;> intro h <;> nlinarith

end CourtadeKumar
