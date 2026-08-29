import InformationTheory.CourtadeKumar.LRGlobalFlowIntegration

/-!
# The canonical target-root trajectory

This module reduces `LRRegularTargetRootTrajectoryTheorem` to the
analytic regularity of one completely specified selector.  There is no new
root-existence assumption here: at every positive prefix we choose the unique
physical root already supplied by `existsUnique_lrPrefixTargetRoot_of_final_physical`.

The pointwise work below proves, for that selector:

* strict physicality at every positive prefix;
* the target equation;
* the prescribed values at `R = 0` and `R = Rmax`;
* uniqueness among all physical roots.

After those facts, the genuinely analytic root obligations are exactly:

1. continuity within the closed prefix interval at its two endpoints;
2. differentiability at every interior prefix.

Continuity of the reserve composition is proved below directly from root
continuity and the closed formula, so it is not an additional hypothesis.

For the interior obligation, `lrCanonicalTargetEquation_sndDeriv_neg` proves
the required transversality.  Thus an implicit-function proof still needs only
the local `C^1` regularity of the two-variable target equation.  The existing
`hasDerivAt_targetRootVelocity` cannot provide this: it assumes that the root
curve already has a derivative.
-/

open Set

namespace CourtadeKumar

lemma lrPrefix_sqrt_mul_sq
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    Real.sqrt (R * t ^ 2) = Real.sqrt R * t := by
  rw [Real.sqrt_mul hR, Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

/-- The data from which the canonical positive-prefix root is selected. -/
structure LRCanonicalTargetRootData (p t Rmax vfinal : ℝ) : Prop where
  hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)
  ht : t ∈ Ioo (0 : ℝ) 1
  hRmax : Rmax ∈ Ioo (0 : ℝ) 1
  hvfinal : vfinal ∈ Ioo (0 : ℝ) 1
  huvfinal : lrProbabilityToOdds p ≤ vfinal
  hrootFinal :
    lrPrefixEll Rmax p = lrSquareTarget Rmax vfinal t

namespace LRCanonicalTargetRootData

variable {p t Rmax vfinal : ℝ}

/-- Strictness of the final physical root propagates to a strict upper
bracket at every earlier prefix.  This is what upgrades the old `Icc` root
to the strict physical interval needed by the global flow. -/
theorem strict_upperBracket
    (D : LRCanonicalTargetRootData p t Rmax vfinal) :
    ∀ R ∈ Ioc (0 : ℝ) Rmax,
      lrGShape (Real.sqrt R * t) 1 < lrPrefixEll R p := by
  have htSq : t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [D.ht.1, D.ht.2]
  have hsqrtMaxPos : 0 < Real.sqrt Rmax := Real.sqrt_pos.2 D.hRmax.1
  have hsqrtMaxLt : Real.sqrt Rmax < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff D.hRmax.1.le).2 D.hRmax.2
  have haMax : Real.sqrt Rmax * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hsqrtMaxPos D.ht.1
    · calc
        Real.sqrt Rmax * t < 1 * t :=
          mul_lt_mul_of_pos_right hsqrtMaxLt D.ht.1
        _ < 1 := by simpa using D.ht.2
  have honeCap : (1 : ℝ) < (Real.sqrt Rmax * t)⁻¹ := by
    rw [one_lt_inv₀ haMax.1]
    exact haMax.2
  have hvDomain :
      vfinal ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
    ⟨D.hvfinal.1, D.hvfinal.2.trans honeCap⟩
  have honeDomain :
      (1 : ℝ) ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
    ⟨by norm_num, honeCap⟩
  have hstrictFinal :
      lrGShape (Real.sqrt Rmax * t) 1 <
        lrGShape (Real.sqrt Rmax * t) vfinal :=
    (strictAntiOn_lrGShape haMax) hvDomain honeDomain D.hvfinal.2
  have hslackFinal : lrPrefixUpperSlack p (t ^ 2) Rmax < 0 := by
    rw [lrPrefixUpperSlack_eq,
      lrPrefix_sqrt_mul_sq D.hRmax.1.le D.ht.1.le]
    rw [D.hrootFinal]
    change
      lrGShape (Real.sqrt Rmax * t) 1 -
        lrGShape (Real.sqrt Rmax * t) vfinal < 0
    exact sub_neg.mpr hstrictFinal
  have hmono := monotoneOn_lrPrefixUpperSlack
    ⟨D.hp.1, D.hp.2.le⟩ htSq D.hRmax
  intro R hR
  have hle := hmono
    ⟨hR.1.le, hR.2⟩
    ⟨D.hRmax.1.le, le_rfl⟩ hR.2
  have hslackR : lrPrefixUpperSlack p (t ^ 2) R < 0 :=
    hle.trans_lt hslackFinal
  rw [lrPrefixUpperSlack_eq,
    lrPrefix_sqrt_mul_sq hR.1.le D.ht.1.le] at hslackR
  exact sub_neg.mp hslackR

/-- Every positive prefix has a unique root in the half-open physical
interval.  Unlike the older pointwise theorem, the upper endpoint is now
strict, as required by `LRRegularTargetRootTrajectory.root_physical`. -/
theorem existsUnique_targetRoot
    (D : LRCanonicalTargetRootData p t Rmax vfinal) :
    ∀ R ∈ Ioc (0 : ℝ) Rmax,
      ∃! v : ℝ,
        v ∈ Ico (lrProbabilityToOdds p) 1 ∧
          lrPrefixEll R p = lrSquareTarget R v t := by
  have htSq : t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [D.ht.1, D.ht.2]
  have hvfinalClosed :
      vfinal ∈ Icc (lrProbabilityToOdds p) 1 :=
    ⟨D.huvfinal, D.hvfinal.2.le⟩
  have hrootFinalOld :
      lrGShape (Real.sqrt (Rmax * t ^ 2)) vfinal =
        lrPrefixEll Rmax p := by
    rw [lrPrefix_sqrt_mul_sq D.hRmax.1.le D.ht.1.le]
    simpa [lrSquareTarget] using D.hrootFinal.symm
  have hroots := existsUnique_lrPrefixTargetRoot_of_final_physical
    D.hp htSq D.hRmax hvfinalClosed hrootFinalOld
  intro R hR
  obtain ⟨v, ⟨hv, hvalueOld⟩, huniqueOld⟩ := hroots R hR
  have hsqrtR := lrPrefix_sqrt_mul_sq hR.1.le D.ht.1.le
  have hvalue : lrPrefixEll R p = lrSquareTarget R v t := by
    change lrPrefixEll R p = lrGShape (Real.sqrt R * t) v
    rw [← hsqrtR]
    exact hvalueOld.symm
  have hvalueOld' :
      lrGShape (Real.sqrt R * t) v = lrPrefixEll R p := by
    rw [← hsqrtR]
    exact hvalueOld
  have hvLt : v < 1 := by
    by_contra hnot
    have hvOne : v = 1 := le_antisymm hv.2 (le_of_not_gt hnot)
    rw [hvOne] at hvalueOld'
    exact (ne_of_lt (D.strict_upperBracket R hR)) hvalueOld'
  refine ⟨v, ⟨⟨hv.1, hvLt⟩, hvalue⟩, ?_⟩
  intro w hw
  apply huniqueOld w
  refine ⟨⟨hw.1.1, hw.1.2.le⟩, ?_⟩
  change
    lrGShape (Real.sqrt (R * t ^ 2)) w = lrPrefixEll R p
  rw [hsqrtR]
  exact hw.2.symm

/-- The canonical selector: input odds at `R = 0`, and the unique strict
physical target root at every positive prefix.  Its proof arguments are
propositionally irrelevant, so this is a canonical mathematical function. -/
noncomputable def root
    (D : LRCanonicalTargetRootData p t Rmax vfinal) (R : ℝ) : ℝ :=
  if hR : R ∈ Ioc (0 : ℝ) Rmax then
    (D.existsUnique_targetRoot R hR).choose
  else
    lrProbabilityToOdds p

@[simp] theorem root_zero
    (D : LRCanonicalTargetRootData p t Rmax vfinal) :
    D.root 0 = lrProbabilityToOdds p := by
  simp [root]

theorem root_spec
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R : ℝ} (hR : R ∈ Ioc (0 : ℝ) Rmax) :
    D.root R ∈ Ico (lrProbabilityToOdds p) 1 ∧
      lrPrefixEll R p = lrSquareTarget R (D.root R) t := by
  rw [root, dif_pos hR]
  exact (D.existsUnique_targetRoot R hR).choose_spec.1

theorem root_eq_of_physical_target
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R v : ℝ} (hR : R ∈ Ioc (0 : ℝ) Rmax)
    (hv : v ∈ Ico (lrProbabilityToOdds p) 1)
    (hvalue : lrPrefixEll R p = lrSquareTarget R v t) :
    D.root R = v := by
  exact (D.existsUnique_targetRoot R hR).unique
    (D.root_spec hR) ⟨hv, hvalue⟩

@[simp] theorem root_final
    (D : LRCanonicalTargetRootData p t Rmax vfinal) :
    D.root Rmax = vfinal := by
  apply D.root_eq_of_physical_target
  · exact ⟨D.hRmax.1, le_rfl⟩
  · exact ⟨D.huvfinal, D.hvfinal.2⟩
  · exact D.hrootFinal

theorem root_physical
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R : ℝ} (hR : R ∈ Ioc (0 : ℝ) Rmax) :
    D.root R ∈ Ioo (0 : ℝ) 1 := by
  have hu := lrProbabilityToOdds_mem_Ioo D.hp
  have hspec := (D.root_spec hR).1
  exact ⟨hu.1.trans_le hspec.1, hspec.2⟩

theorem root_target_eq
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R : ℝ} (hR : R ∈ Ioc (0 : ℝ) Rmax) :
    lrPrefixEll R p = lrSquareTarget R (D.root R) t :=
  (D.root_spec hR).2

/-- Interior differentiability plus continuity at the two relative endpoints
is exactly enough to recover closed-interval continuity. -/
theorem root_continuousOn_of_endpoint_continuity_and_differentiable
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    (hzero : ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) 0)
    (hfinal : ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) Rmax)
    (hdiff : ∀ R ∈ Ioo (0 : ℝ) Rmax,
      DifferentiableAt ℝ D.root R) :
    ContinuousOn D.root (Icc (0 : ℝ) Rmax) := by
  intro R hR
  by_cases hRzero : R = 0
  · simpa [hRzero] using hzero
  by_cases hRfinal : R = Rmax
  · simpa [hRfinal] using hfinal
  have hRpos : 0 < R :=
    lt_of_le_of_ne hR.1 (Ne.symm hRzero)
  have hRlt : R < Rmax := lt_of_le_of_ne hR.2 hRfinal
  exact (hdiff R ⟨hRpos, hRlt⟩).continuousAt.continuousWithinAt

/-- Continuity of normalized energy along any continuous auxiliary curve,
away from the sole channel denominator `R = 1`. -/
theorem continuousWithinAt_lrNormalizedEnergy_comp
    {s : Set ℝ} {R : ℝ} {z : ℝ → ℝ}
    (hz : ContinuousWithinAt z s R)
    (hden : 1 - R ≠ 0) :
    ContinuousWithinAt
      (fun y : ℝ ↦ lrNormalizedEnergy y (z y)) s R := by
  have hsqrt : ContinuousWithinAt (fun y : ℝ ↦ Real.sqrt y) s R :=
    Real.continuous_sqrt.continuousWithinAt
  have hphiZ : ContinuousWithinAt (fun y : ℝ ↦ topPhi (z y)) s R :=
    continuous_topPhi.continuousAt.comp_continuousWithinAt hz
  have hsqrtZ :
      ContinuousWithinAt (fun y : ℝ ↦ Real.sqrt y * z y) s R :=
    hsqrt.mul hz
  have hphiSqrtZ :
      ContinuousWithinAt
        (fun y : ℝ ↦ topPhi (Real.sqrt y * z y)) s R :=
    continuous_topPhi.continuousAt.comp_continuousWithinAt hsqrtZ
  unfold lrNormalizedEnergy
  exact ((continuousWithinAt_id.mul hphiZ).sub hphiSqrtZ).div
    (continuousWithinAt_const.sub continuousWithinAt_id) hden

/-- Continuity of the perspective term along any curve which is nonzero at
the point under consideration. -/
theorem continuousWithinAt_lrPhiPerspective_comp
    {s : Set ℝ} {R t : ℝ} {v : ℝ → ℝ}
    (hv : ContinuousWithinAt v s R)
    (hvne : v R ≠ 0) :
    ContinuousWithinAt
      (fun y : ℝ ↦ lrPhiPerspective (v y) t) s R := by
  have harg : ContinuousWithinAt (fun y : ℝ ↦ v y * t) s R :=
    hv.mul continuousWithinAt_const
  have hphi : ContinuousWithinAt (fun y : ℝ ↦ topPhi (v y * t)) s R :=
    continuous_topPhi.continuousAt.comp_continuousWithinAt harg
  unfold lrPhiPerspective
  exact hphi.div hv hvne

/-- The closed squared-coordinate reserve is continuous along every
continuous positive root curve below the singular channel endpoint. -/
theorem continuousWithinAt_lrSquareReserve_comp
    {s : Set ℝ} {R u t : ℝ} {v : ℝ → ℝ}
    (hv : ContinuousWithinAt v s R)
    (hvpos : 0 < v R)
    (hden : 1 - R ≠ 0) :
    ContinuousWithinAt
      (fun y : ℝ ↦ lrSquareReserve y u (v y) t) s R := by
  have hperspectiveV :=
    continuousWithinAt_lrPhiPerspective_comp (t := t) hv hvpos.ne'
  have henergyT : ContinuousWithinAt
      (fun y : ℝ ↦ lrNormalizedEnergy y t) s R :=
    continuousWithinAt_lrNormalizedEnergy_comp
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ ↦ t) s R) hden
  have hvt : ContinuousWithinAt (fun y : ℝ ↦ v y * t) s R :=
    hv.mul continuousWithinAt_const
  have henergyVT :=
    continuousWithinAt_lrNormalizedEnergy_comp hvt hden
  have henergyVTdiv : ContinuousWithinAt
      (fun y : ℝ ↦ lrNormalizedEnergy y (v y * t) / v y) s R :=
    henergyVT.div hv hvpos.ne'
  have hfirst : ContinuousWithinAt
      (fun y : ℝ ↦ 1 / t ^ 2 *
        (lrPhiPerspective (v y) t - lrPhiPerspective u t)) s R :=
    continuousWithinAt_const.mul
      (hperspectiveV.sub continuousWithinAt_const)
  have hsecond : ContinuousWithinAt
      (fun y : ℝ ↦ 1 / t ^ 2 *
        (lrNormalizedEnergy y t +
          lrNormalizedEnergy y (v y * t) / v y)) s R :=
    continuousWithinAt_const.mul (henergyT.add henergyVTdiv)
  have henergyOne : ContinuousWithinAt
      (fun y : ℝ ↦ lrNormalizedEnergy y 1) s R :=
    continuousWithinAt_lrNormalizedEnergy_comp
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ ↦ (1 : ℝ)) s R) hden
  have hpenalty : ContinuousWithinAt
      (fun y : ℝ ↦
        4 * lrNormalizedEnergy y 1 * u / (1 + u)) s R :=
    ((continuousWithinAt_const.mul henergyOne).mul
      continuousWithinAt_const).div_const (1 + u)
  unfold lrSquareReserve lrQSquare
  exact (hfirst.add hsecond).sub hpenalty

/-- Consequently the reserve-continuity field is not an additional analytic
hypothesis: it follows pointwise from closed-interval root continuity. -/
theorem reserve_continuousOn_of_root_continuousOn
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    (hroot : ContinuousOn D.root (Icc (0 : ℝ) Rmax)) :
    ContinuousOn
      (fun R : ℝ ↦
        lrSquareReserve R (lrProbabilityToOdds p) (D.root R) t)
      (Icc (0 : ℝ) Rmax) := by
  intro R hR
  have hrootPos : 0 < D.root R := by
    by_cases hRzero : R = 0
    · rw [hRzero, D.root_zero]
      exact (lrProbabilityToOdds_mem_Ioo D.hp).1
    · exact (D.root_physical
        ⟨lt_of_le_of_ne hR.1 (Ne.symm hRzero), hR.2⟩).1
  have hden : 1 - R ≠ 0 := by
    have : R < 1 := hR.2.trans_lt D.hRmax.2
    exact sub_ne_zero.mpr this.ne'
  exact continuousWithinAt_lrSquareReserve_comp
    (hroot R hR) hrootPos hden

/-- Once the honest root-regularity obligations are supplied, every field of
the tracked global trajectory is filled by the canonical selector. -/
theorem nonempty_regularTargetRootTrajectory
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    (hzero : ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) 0)
    (hfinal : ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) Rmax)
    (hdiff : ∀ R ∈ Ioo (0 : ℝ) Rmax,
      DifferentiableAt ℝ D.root R) :
    Nonempty (LRRegularTargetRootTrajectory p t Rmax vfinal) := by
  have hrootContinuous :=
    D.root_continuousOn_of_endpoint_continuity_and_differentiable
      hzero hfinal hdiff
  exact ⟨{
    root := D.root
    root_zero := D.root_zero
    root_final := D.root_final
    root_physical := fun R hR ↦ D.root_physical hR
    target_eq := fun R hR ↦ D.root_target_eq hR
    root_continuousOn := hrootContinuous
    root_differentiableAt := hdiff
    reserve_continuousOn :=
      D.reserve_continuousOn_of_root_continuousOn hrootContinuous
  }⟩

end LRCanonicalTargetRootData

/-- The fundamental analytic input for the now-fixed canonical selector.
Interior differentiability supplies interior continuity, so only relative
continuity at the two endpoints is stated separately. -/
def LRCanonicalTargetRootRegularityTheorem : Prop :=
  ∀ (p t Rmax vfinal : ℝ)
    (D : LRCanonicalTargetRootData p t Rmax vfinal),
    ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) 0 ∧
      ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) Rmax ∧
        ∀ R ∈ Ioo (0 : ℝ) Rmax, DifferentiableAt ℝ D.root R

/-- The tracked global trajectory input follows from regularity of the one
canonical selector.  All existence, uniqueness, physicality, target-equation,
endpoint-value, and reserve-continuity fields have been discharged above. -/
theorem regularTargetRootTrajectories_of_canonical
    (hregular : LRCanonicalTargetRootRegularityTheorem) :
    LRRegularTargetRootTrajectoryTheorem := by
  intro p t Rmax vfinal hp ht hRmax hvfinal huvfinal hrootFinal
  let D : LRCanonicalTargetRootData p t Rmax vfinal := {
    hp := hp
    ht := ht
    hRmax := hRmax
    hvfinal := hvfinal
    huvfinal := huvfinal
    hrootFinal := hrootFinal
  }
  obtain ⟨hzero, hfinal, hdiff⟩ := hregular p t Rmax vfinal D
  exact D.nonempty_regularTargetRootTrajectory hzero hfinal hdiff

/-- Strongest end-to-end theorem exposed by the canonical-root reduction.
After the pointwise flow numerator, the sole remaining global analytic input
is endpoint continuity and interior differentiability of the canonical unique
target-root selector. -/
theorem courtadeKumar_of_targetFlow_and_canonicalRootRegularity
    (hflow : LRTargetFlowNumeratorTheorem)
    (hregular : LRCanonicalTargetRootRegularityTheorem) :
    Statement := by
  exact courtadeKumar_of_targetFlow_regularTrajectories hflow
    (regularTargetRootTrajectories_of_canonical hregular)

/-- The target equation as a two-variable scalar function.  Its zero set is
the graph of the positive-prefix canonical selector. -/
noncomputable def lrCanonicalTargetEquation
    (p t : ℝ) (z : ℝ × ℝ) : ℝ :=
  lrSquareTarget z.1 z.2 t - lrPrefixEll z.1 p

/-- The derivative in the root variable is strictly negative throughout the
physical region.  This is the nondegeneracy input for the implicit-function
theorem; what remains is to package local `C^1` regularity in both variables.
-/
theorem lrCanonicalTargetEquation_sndDeriv_neg
    {p t R v : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (fun q : ℝ ↦ lrCanonicalTargetEquation p t (R, q)) v < 0 := by
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have ha0 : 0 ≤ Real.sqrt R * t :=
    mul_nonneg (Real.sqrt_nonneg R) ht.1.le
  have hav : (Real.sqrt R * t) * v < 1 := by
    calc
      (Real.sqrt R * t) * v = Real.sqrt R * (v * t) := by ring
      _ < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 * t := by
        simpa using (mul_lt_mul_of_pos_right hv.2 ht.1)
      _ < 1 := by simpa using ht.2
  have hderiv := hasDerivAt_lrGShape hv.1 ha0 hav
  have hneg := deriv_lrGShape_neg hv.1 ha0 hav
  have heq :
      deriv (fun q : ℝ ↦ lrCanonicalTargetEquation p t (R, q)) v =
        deriv (lrGShape (Real.sqrt R * t)) v := by
    have hleft : HasDerivAt
        (fun q : ℝ ↦ lrCanonicalTargetEquation p t (R, q))
        (-(Real.log (1 + v) + lrL ((Real.sqrt R * t) * v)) / v ^ 2) v := by
      simpa [lrCanonicalTargetEquation, lrSquareTarget] using
        hderiv.sub_const (lrPrefixEll R p)
    rw [hleft.deriv, hderiv.deriv]
  rw [heq]
  exact hneg

theorem lrCanonicalTargetEquation_sndDeriv_ne_zero
    {p t R v : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (fun q : ℝ ↦ lrCanonicalTargetEquation p t (R, q)) v ≠ 0 :=
  (lrCanonicalTargetEquation_sndDeriv_neg hR ht hv).ne

end CourtadeKumar
