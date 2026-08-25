import InformationTheory.CourtadeKumar.LRReserve
import InformationTheory.CourtadeKumar.TopCapPrimitive

open Set
open scoped NNReal

namespace CourtadeKumar

noncomputable def lrProbabilityToOdds (p : ℝ) : ℝ := p / (1 - p)

lemma lrOddsToProbability_probabilityToOdds
    {p : ℝ} (hp : p < 1) :
    lrOddsToProbability (lrProbabilityToOdds p) = p := by
  have hden : 1 - p ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hsum : 1 + p / (1 - p) = 1 / (1 - p) := by
    field_simp [hden]
    ring
  unfold lrOddsToProbability lrProbabilityToOdds
  rw [hsum]
  field_simp [hden]

lemma lrProbabilityToOdds_mem_Ioo
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    lrProbabilityToOdds p ∈ Ioo (0 : ℝ) 1 := by
  unfold lrProbabilityToOdds
  constructor
  · exact div_pos hp.1 (sub_pos.mpr (hp.2.trans (by norm_num)))
  · rw [div_lt_one (by linarith [hp.2])]
    linarith [hp.2]

noncomputable def lrPrefixEll (R p : ℝ) : ℝ :=
  (1 - R) * Real.binEntropy p / p +
    4 * (R * Real.log 2 - topPhi (Real.sqrt R)) * (1 - p)

noncomputable def lrPrefixUpperSlack (p x R : ℝ) : ℝ :=
  2 * Real.log 2 - 2 * topPhi (Real.sqrt (R * x)) - lrPrefixEll R p

noncomputable def lrPrefixUpperSlackDeriv (p x R : ℝ) : ℝ :=
  Real.binEntropy p / p - 4 * (1 - p) * Real.log 2 +
    4 * (1 - p) * topPsiDeriv R - 2 * x * topPsiDeriv (R * x)

lemma lrPrefixEll_eq_lrObjectiveTarget
    {R p : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    lrPrefixEll R p =
      lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) := by
  have hsqrt : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hp1 : p < 1 := hp.2.trans (by norm_num)
  have hu : 0 < lrProbabilityToOdds p :=
    (lrProbabilityToOdds_mem_Ioo hp).1
  have hprob := lrOddsToProbability_probabilityToOdds hp1
  have hG := lrG_eq_binEntropy_div hu
  rw [hprob] at hG
  unfold lrPrefixEll lrObjectiveTarget lrMu topEnergy topS topR
  rw [hG, hsqrt, topPhi_one]
  unfold lrProbabilityToOdds
  have hp0 : p ≠ 0 := hp.1.ne'
  have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.ne'
  have hRone : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  field_simp [hp0, hpOne, hRone]
  ring

theorem hasDerivAt_lrPrefixUpperSlack
    {p x R : ℝ} (hp : 0 < p) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrPrefixUpperSlack p x)
      (lrPrefixUpperSlackDeriv p x R) R := by
  have hRx : R * x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hx.1
    · calc
        R * x < 1 * x := mul_lt_mul_of_pos_right hR.2 hx.1
        _ < 1 := by simpa using hx.2
  have harg : HasDerivAt (fun y : ℝ ↦ y * x) x R := by
    simpa using (hasDerivAt_id R).mul_const x
  have hphiRx := (hasDerivAt_topPsi hRx).comp R harg
  have hphiR := hasDerivAt_topPsi hR
  have hlinear := (hasDerivAt_id R).mul_const (Real.log 2)
  have hlambda := hlinear.sub hphiR
  have honeMinus := (hasDerivAt_const R 1).sub (hasDerivAt_id R)
  have hell :=
    ((honeMinus.mul_const (Real.binEntropy p)).div_const p).add
      (hlambda.const_mul 4 |>.mul_const (1 - p))
  have hslack :=
    ((hasDerivAt_const R (2 * Real.log 2)).sub
      (hphiRx.const_mul 2)).sub hell
  convert hslack using 1
  simp only [lrPrefixUpperSlackDeriv]
  field_simp [hp.ne']
  ring

lemma half_le_topPsiDeriv {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    1 / 2 ≤ topPsiDeriv R := by
  have hsqrtPos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hart := self_lt_artanh ⟨hsqrtPos, hsqrtLt⟩
  unfold topPsiDeriv
  rw [le_div_iff₀ (mul_pos (by norm_num) hsqrtPos)]
  nlinarith

lemma lrPrefixEntropyRemainder_nonneg
    {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ)) :
    0 ≤ Real.binEntropy p - 4 * p * (1 - p) * Real.log 2 + p - 2 * p ^ 2 := by
  let rho : ℝ := 1 - 2 * p
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    dsimp [rho]
    constructor <;> linarith [hp.1, hp.2]
  have hell := topEll_nonneg hrho
  have hid : topEll rho =
      Real.binEntropy p - 4 * p * (1 - p) * Real.log 2 := by
    unfold topEll topR topPhi
    dsimp [rho]
    rw [show (1 - (1 - 2 * p)) / 2 = p by ring]
    ring
  rw [hid] at hell
  have hquad : 0 ≤ p - 2 * p ^ 2 := by
    nlinarith [hp.1, hp.2]
  linarith

theorem lrPrefixUpperSlackDeriv_nonneg
    {p x R : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrPrefixUpperSlackDeriv p x R := by
  have hRx : R * x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hx.1
    · calc
        R * x < R * 1 := mul_lt_mul_of_pos_left hx.2 hR.1
        _ < 1 := by simpa using hR.2
  have hmono := topPsiDeriv_monotoneOn hRx hR
    (mul_le_of_le_one_right hR.1.le hx.2.le)
  have hpsi0 : 0 ≤ topPsiDeriv (R * x) :=
    (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (half_le_topPsiDeriv hRx)
  have hxscale : x * topPsiDeriv (R * x) ≤ topPsiDeriv R := by
    calc
      x * topPsiDeriv (R * x) ≤ 1 * topPsiDeriv (R * x) :=
        mul_le_mul_of_nonneg_right hx.2.le hpsi0
      _ ≤ topPsiDeriv R := by simpa using hmono
  have hpsiHalf := half_le_topPsiDeriv hR
  have hpcoef : 0 ≤ 2 - 4 * p := by linarith [hp.2]
  have henergy :
      1 - 2 * p ≤
        4 * (1 - p) * topPsiDeriv R -
          2 * x * topPsiDeriv (R * x) := by
    nlinarith
  have hentropy := lrPrefixEntropyRemainder_nonneg hp
  have hp0 : p ≠ 0 := hp.1.ne'
  have hentropyDiv :
      0 ≤ Real.binEntropy p / p -
        4 * (1 - p) * Real.log 2 + 1 - 2 * p := by
    have hdiv := div_nonneg hentropy hp.1.le
    convert hdiv using 1
    field_simp [hp0]
  unfold lrPrefixUpperSlackDeriv
  nlinarith

lemma lrGShape_one (a : ℝ) :
    lrGShape a 1 = 2 * Real.log 2 - 2 * topPhi a := by
  unfold lrGShape lrG
  norm_num
  ring

lemma lrPrefixUpperSlack_eq (p x R : ℝ) :
    lrPrefixUpperSlack p x R =
      lrGShape (Real.sqrt (R * x)) 1 - lrPrefixEll R p := by
  rw [lrGShape_one]
  rfl

/-- The upper-endpoint slack is nondecreasing along every positive noise
prefix, exactly as in the manuscript's prefix-physicality lemma. -/
theorem monotoneOn_lrPrefixUpperSlack
    {p x Rmax : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1) :
    MonotoneOn (lrPrefixUpperSlack p x) (Icc (0 : ℝ) Rmax) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) Rmax)
  · have harg : Continuous (fun R : ℝ ↦ R * x) :=
      continuous_id.mul continuous_const
    have hphiRx : Continuous (fun R : ℝ ↦ topPhi (Real.sqrt (R * x))) :=
      continuous_topPhi.comp (Real.continuous_sqrt.comp harg)
    have hphiR : Continuous (fun R : ℝ ↦ topPhi (Real.sqrt R)) :=
      continuous_topPhi.comp Real.continuous_sqrt
    have hfirst : Continuous (fun R : ℝ ↦
        2 * Real.log 2 - 2 * topPhi (Real.sqrt (R * x))) :=
      continuous_const.sub (continuous_const.mul hphiRx)
    have hellFirst : Continuous (fun R : ℝ ↦
        (1 - R) * Real.binEntropy p / p) :=
      ((continuous_const.sub continuous_id).mul continuous_const).div_const p
    have hellSecond : Continuous (fun R : ℝ ↦
        4 * (R * Real.log 2 - topPhi (Real.sqrt R)) * (1 - p)) :=
      (continuous_const.mul
        ((continuous_id.mul continuous_const).sub hphiR)).mul continuous_const
    exact (hfirst.sub (hellFirst.add hellSecond)).continuousOn
  · intro R hR
    rw [interior_Icc] at hR
    have hR' : R ∈ Ioo (0 : ℝ) 1 :=
      ⟨hR.1, hR.2.trans hRmax.2⟩
    exact (hasDerivAt_lrPrefixUpperSlack hp.1 hx hR').hasDerivWithinAt
  · intro R hR
    rw [interior_Icc] at hR
    exact lrPrefixUpperSlackDeriv_nonneg hp hx
      ⟨hR.1, hR.2.trans hRmax.2⟩

theorem lrPrefix_upperBracket
    {p x Rmax : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1)
    (hfinal : lrGShape (Real.sqrt (Rmax * x)) 1 ≤
      lrPrefixEll Rmax p) :
    ∀ R ∈ Icc (0 : ℝ) Rmax,
      lrGShape (Real.sqrt (R * x)) 1 ≤ lrPrefixEll R p := by
  intro R hR
  have hmono := monotoneOn_lrPrefixUpperSlack hp hx hRmax hR
    (show Rmax ∈ Icc (0 : ℝ) Rmax from ⟨hRmax.1.le, le_rfl⟩) hR.2
  rw [lrPrefixUpperSlack_eq, lrPrefixUpperSlack_eq] at hmono
  linarith

/-- The pointwise radial boundary theorem gives the lower bracket needed
for every physical prefix root. -/
theorem lrPrefix_lowerBracket
    {p x R : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrPrefixEll R p ≤
      lrGShape (Real.sqrt (R * x)) (lrProbabilityToOdds p) := by
  let rho := Real.sqrt R
  let t := Real.sqrt x
  let alpha : ℝ≥0 := ⟨(1 - rho) / 2, by
    have hrho1 : rho < 1 := by
      dsimp [rho]
      simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
    exact div_nonneg (sub_nonneg.mpr hrho1.le) (by norm_num)⟩
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    constructor
    · exact Real.sqrt_pos.2 hR.1
    · simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    dsimp [t]
    constructor
    · exact Real.sqrt_pos.2 hx.1
    · simpa using (Real.sqrt_lt_sqrt_iff hx.1.le).2 hx.2
  have halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := by
    dsimp [alpha]
    constructor <;> nlinarith [hrho.1, hrho.2]
  have hchannel : channelRho (alpha : ℝ) = rho := by
    dsimp [alpha]
    unfold channelRho
    ring
  have hbit := bellmanEnvelope_le_radialChannelEntropy
    halpha ⟨ht.1.le, ht.2.le⟩ ⟨hp.1.le, hp.2.le⟩
  have hnat : lowerRayNatEnvelope rho p ≤ radialNatEntropy rho t p := by
    rw [← hchannel, lowerRayNatEnvelope_eq_bellman]
    calc
      Real.log 2 * bellmanEnvelope (alpha : ℝ) p ≤
          Real.log 2 * radialTriangleChannelEntropy alpha t p :=
        mul_le_mul_of_nonneg_left hbit (Real.log_pos one_lt_two).le
      _ = radialNatEntropy (channelRho (alpha : ℝ)) t p := by
        rw [radialTriangleChannelEntropy_eq_nat]
        field_simp [log_two_ne_zero]
  let u := lrProbabilityToOdds p
  have hu : u ∈ Ioo (0 : ℝ) 1 := lrProbabilityToOdds_mem_Ioo hp
  have hprob : lrOddsToProbability u = p := by
    dsimp [u]
    exact lrOddsToProbability_probabilityToOdds
      (hp.2.trans (by norm_num))
  have hleft :
      lowerRayNatEnvelope rho (lrOddsToProbability u) ≤
        lrOddsToProbability u / lrOddsToProbability u *
          radialNatEntropy rho t (lrOddsToProbability u) := by
    rw [hprob]
    simpa [hp.1.ne'] using hnat
  have htarget :=
    (singleRayNatLR_iff_lrObjectiveTarget hrho hu
      ⟨hu.1, hu.2.le⟩ ht).mp hleft
  have hell := lrPrefixEll_eq_lrObjectiveTarget hR hp
  have hsqrtMul : Real.sqrt (R * x) = rho * t := by
    dsimp [rho, t]
    exact Real.sqrt_mul hR.1.le x
  rw [hell, hsqrtMul]
  simpa [u] using htarget

theorem existsUnique_lrPrefixTargetRoot
    {p x R u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hlower : lrPrefixEll R p ≤ lrGShape (Real.sqrt (R * x)) u)
    (hupper : lrGShape (Real.sqrt (R * x)) 1 ≤ lrPrefixEll R p) :
    ∃! v : ℝ, v ∈ Icc u 1 ∧
      lrGShape (Real.sqrt (R * x)) v = lrPrefixEll R p := by
  have hRx : R * x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hR.1 hx.1
    · calc
        R * x < R * 1 := mul_lt_mul_of_pos_left hx.2 hR.1
        _ < 1 := by simpa using hR.2
  have ha : Real.sqrt (R * x) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hRx.1
    · simpa using (Real.sqrt_lt_sqrt_iff hRx.1.le).2 hRx.2
  exact existsUnique_lrGShape_eq_of_bracket ha hu hupper hlower

/-- Physicality of every positive target-root prefix.  The lower bracket is
the already separated pointwise-boundary input; the upper bracket propagates
from the final physical root by the monotone slack theorem. -/
theorem existsUnique_lrPrefixTargetRoot_of_final
    {p x Rmax u vfinal : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1)
    (hvfinal : vfinal ∈ Icc u 1)
    (hrootFinal : lrGShape (Real.sqrt (Rmax * x)) vfinal =
      lrPrefixEll Rmax p)
    (hlower : ∀ R ∈ Ioc (0 : ℝ) Rmax,
      lrPrefixEll R p ≤ lrGShape (Real.sqrt (R * x)) u) :
    ∀ R ∈ Ioc (0 : ℝ) Rmax,
      ∃! v : ℝ, v ∈ Icc u 1 ∧
        lrGShape (Real.sqrt (R * x)) v = lrPrefixEll R p := by
  have hRmaxX : Rmax * x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hRmax.1 hx.1
    · calc
        Rmax * x < Rmax * 1 := mul_lt_mul_of_pos_left hx.2 hRmax.1
        _ < 1 := by simpa using hRmax.2
  have haMax : Real.sqrt (Rmax * x) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hRmaxX.1
    · simpa using (Real.sqrt_lt_sqrt_iff hRmaxX.1.le).2 hRmaxX.2
  have honeCap : (1 : ℝ) < (Real.sqrt (Rmax * x))⁻¹ := by
    rw [one_lt_inv₀ haMax.1]
    exact haMax.2
  have hvDomain : vfinal ∈ Ioo (0 : ℝ) (Real.sqrt (Rmax * x))⁻¹ :=
    ⟨hu.1.trans_le hvfinal.1, hvfinal.2.trans_lt honeCap⟩
  have honeDomain : (1 : ℝ) ∈
      Ioo (0 : ℝ) (Real.sqrt (Rmax * x))⁻¹ := ⟨by norm_num, honeCap⟩
  have hfinal : lrGShape (Real.sqrt (Rmax * x)) 1 ≤
      lrPrefixEll Rmax p := by
    rw [← hrootFinal]
    exact (strictAntiOn_lrGShape haMax).antitoneOn
      hvDomain honeDomain hvfinal.2
  have hupper := lrPrefix_upperBracket hp hx hRmax hfinal
  intro R hR
  exact existsUnique_lrPrefixTargetRoot hu hx
    ⟨hR.1, hR.2.trans_lt hRmax.2⟩ (hlower R hR)
    (hupper R ⟨hR.1.le, hR.2⟩)

/-- Every positive prefix of a final physical target root has a unique
physical root.  Both brackets are discharged here: the lower one by the
pointwise radial boundary theorem, and the upper one by monotone slack. -/
theorem existsUnique_lrPrefixTargetRoot_of_final_physical
    {p x Rmax vfinal : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1)
    (hvfinal : vfinal ∈ Icc (lrProbabilityToOdds p) 1)
    (hrootFinal : lrGShape (Real.sqrt (Rmax * x)) vfinal =
      lrPrefixEll Rmax p) :
    ∀ R ∈ Ioc (0 : ℝ) Rmax,
      ∃! v : ℝ, v ∈ Icc (lrProbabilityToOdds p) 1 ∧
        lrGShape (Real.sqrt (R * x)) v = lrPrefixEll R p := by
  apply existsUnique_lrPrefixTargetRoot_of_final
    ⟨hp.1, hp.2.le⟩ (lrProbabilityToOdds_mem_Ioo hp) hx hRmax
    hvfinal hrootFinal
  intro R hR
  exact lrPrefix_lowerBracket hp hx ⟨hR.1, hR.2.trans_lt hRmax.2⟩

end CourtadeKumar
