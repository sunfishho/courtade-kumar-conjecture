import InformationTheory.CourtadeKumar.LRGlobalFlowIntegration
import Mathlib.Analysis.Calculus.ImplicitContDiff

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

The unique-root equation and strict monotonicity prove continuity within the
closed prefix interval at both endpoints below.  At `R = 0` the proof uses
exact zero-prefix identities, not an asymptotic expansion.  Local `C^1`
regularity and Mathlib's implicit-function theorem then prove differentiability
at every interior prefix.

Continuity of the reserve composition is proved below directly from root
continuity and the closed formula, so it is not an additional hypothesis.

For the interior argument, `lrCanonicalTargetEquation_sndDeriv_neg` proves the
required transversality.  The local implicit branch agrees with the canonical
selector by strict root uniqueness.  Consequently the global target-root
regularity theorem is unconditional in this module.
-/

open Filter Set
open scoped Topology

namespace CourtadeKumar

lemma lrPrefix_sqrt_mul_sq
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    Real.sqrt (R * t ^ 2) = Real.sqrt R * t := by
  rw [Real.sqrt_mul hR, Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

/-- The prefix target is globally continuous in the squared prefix. -/
lemma continuous_lrPrefixEll_in_prefix (p : ℝ) :
    Continuous (fun R : ℝ ↦ lrPrefixEll R p) := by
  unfold lrPrefixEll
  exact
    (((continuous_const.sub continuous_id).mul continuous_const).div_const p).add
      ((continuous_const.mul
        ((continuous_id.mul continuous_const).sub
          (continuous_topPhi.comp Real.continuous_sqrt))).mul continuous_const)

/-- At a fixed physical root and ray, the scalar target is globally
continuous in the squared prefix. -/
lemma continuous_lrSquareTarget_in_prefix (v t : ℝ) :
    Continuous (fun R : ℝ ↦ lrSquareTarget R v t) := by
  unfold lrSquareTarget lrGShape
  exact
    (continuous_const.sub
      (continuous_topPhi.comp
        (Real.continuous_sqrt.mul continuous_const))).sub
      ((continuous_topPhi.comp
        (continuous_const.mul
          (Real.continuous_sqrt.mul continuous_const))).div_const v)

@[simp] lemma lrSquareTarget_zero (v t : ℝ) :
    lrSquareTarget 0 v t = lrG v := by
  simp [lrSquareTarget, lrGShape]

/-- At the zero prefix the prescribed target is exactly the odds-entropy
quotient at the input odds. -/
lemma lrPrefixEll_zero_eq_lrG_probabilityToOdds
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    lrPrefixEll 0 p = lrG (lrProbabilityToOdds p) := by
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hback : lrOddsToProbability (lrProbabilityToOdds p) = p :=
    lrOddsToProbability_probabilityToOdds (hp.2.trans (by norm_num))
  rw [lrG_eq_binEntropy_div hu.1, hback]
  simp [lrPrefixEll]

/-- The odds-entropy quotient is strictly decreasing on the positive axis. -/
theorem strictAntiOn_lrG_pos : StrictAntiOn lrG (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro q hq
    exact (hasDerivAt_lrG hq).continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ioi] at hq
    rw [(hasDerivAt_lrG hq).deriv]
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos
        (Real.log_pos (by
          simpa using (add_lt_add_left hq (1 : ℝ)))))
      (sq_pos_of_pos hq)

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

/-- The contracted shape stays in its open physical domain at every positive
prefix. -/
lemma prefix_shape_mem_Ioo
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R : ℝ} (hR : R ∈ Ioc (0 : ℝ) Rmax) :
    Real.sqrt R * t ∈ Ioo (0 : ℝ) 1 := by
  have hsqrtPos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR.1
  have hRLt : R < 1 := hR.2.trans_lt D.hRmax.2
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hRLt
  constructor
  · exact mul_pos hsqrtPos D.ht.1
  · calc
      Real.sqrt R * t < 1 * t :=
        mul_lt_mul_of_pos_right hsqrtLt D.ht.1
      _ < 1 := by simpa using D.ht.2

/-- The canonical root lies in the full open domain on which the fixed-shape
target is strictly decreasing. -/
lemma root_mem_shape_domain
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R : ℝ} (hR : R ∈ Ioc (0 : ℝ) Rmax) :
    D.root R ∈ Ioo (0 : ℝ) (Real.sqrt R * t)⁻¹ := by
  have ha := D.prefix_shape_mem_Ioo hR
  have honeCap : (1 : ℝ) < (Real.sqrt R * t)⁻¹ := by
    rw [one_lt_inv₀ ha.1]
    exact ha.2
  have hroot := D.root_physical hR
  exact ⟨hroot.1, hroot.2.trans honeCap⟩

/-- Relative continuity at the final prefix follows from the unique-root
equation and strict decrease in the root variable. -/
theorem root_continuousWithinAt_final
    (D : LRCanonicalTargetRootData p t Rmax vfinal) :
    ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) Rmax := by
  let l : Filter ℝ := nhdsWithin Rmax (Icc (0 : ℝ) Rmax)
  have hself : ∀ᶠ R in l, R ∈ Icc (0 : ℝ) Rmax :=
    self_mem_nhdsWithin
  have hpos : ∀ᶠ R in l, 0 < R :=
    (eventually_gt_nhds D.hRmax.1).filter_mono nhdsWithin_le_nhds
  have hprefix : ∀ᶠ R in l, R ∈ Ioc (0 : ℝ) Rmax := by
    filter_upwards [hself, hpos] with R hR hRpos
    exact ⟨hRpos, hR.2⟩
  have hrootSpec : ∀ᶠ R in l,
      D.root R ∈ Ico (lrProbabilityToOdds p) 1 ∧
        lrPrefixEll R p = lrSquareTarget R (D.root R) t := by
    exact hprefix.mono (fun _ hR ↦ D.root_spec hR)
  have hellTendsto : Tendsto (fun R : ℝ ↦ lrPrefixEll R p) l
      (nhds (lrPrefixEll Rmax p)) :=
    (continuous_lrPrefixEll_in_prefix p).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have haMax := D.prefix_shape_mem_Ioo
    (show Rmax ∈ Ioc (0 : ℝ) Rmax from ⟨D.hRmax.1, le_rfl⟩)
  change Tendsto D.root l (nhds (D.root Rmax))
  rw [D.root_final]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let u : ℝ := lrProbabilityToOdds p
    have hu : u ∈ Ioo (0 : ℝ) 1 := lrProbabilityToOdds_mem_Ioo D.hp
    by_cases hau : a < u
    · exact hrootSpec.mono (fun _ hs ↦ hau.trans_le hs.1.1)
    · have hua : u ≤ a := le_of_not_gt hau
      have haPos : 0 < a := hu.1.trans_le hua
      have haOne : a < 1 := ha.trans D.hvfinal.2
      have honeCap : (1 : ℝ) < (Real.sqrt Rmax * t)⁻¹ := by
        rw [one_lt_inv₀ haMax.1]
        exact haMax.2
      have haDomain : a ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
        ⟨haPos, haOne.trans honeCap⟩
      have hvDomain : vfinal ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
        ⟨D.hvfinal.1, D.hvfinal.2.trans honeCap⟩
      have hstrict : lrSquareTarget Rmax vfinal t <
          lrSquareTarget Rmax a t := by
        change lrGShape (Real.sqrt Rmax * t) vfinal <
          lrGShape (Real.sqrt Rmax * t) a
        exact (strictAntiOn_lrGShape haMax) haDomain hvDomain ha
      have haTendsto : Tendsto (fun R : ℝ ↦ lrSquareTarget R a t) l
          (nhds (lrSquareTarget Rmax a t)) :=
        (continuous_lrSquareTarget_in_prefix a t).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have horder : ∀ᶠ R in l,
          lrPrefixEll R p < lrSquareTarget R a t := by
        apply hellTendsto.eventually_lt haTendsto
        rw [D.hrootFinal]
        exact hstrict
      filter_upwards [hprefix, hrootSpec, horder] with R hR hs horderR
      have haR := D.prefix_shape_mem_Ioo hR
      have hrootDomain := D.root_mem_shape_domain hR
      have honeCapR : (1 : ℝ) < (Real.sqrt R * t)⁻¹ := by
        rw [one_lt_inv₀ haR.1]
        exact haR.2
      have haDomainR : a ∈ Ioo (0 : ℝ) (Real.sqrt R * t)⁻¹ :=
        ⟨haPos, haOne.trans honeCapR⟩
      apply ((strictAntiOn_lrGShape haR).lt_iff_gt
        hrootDomain haDomainR).mp
      change lrSquareTarget R (D.root R) t < lrSquareTarget R a t
      rw [← hs.2]
      exact horderR
  · intro b hb
    by_cases hOneB : (1 : ℝ) ≤ b
    · exact hrootSpec.mono (fun _ hs ↦ hs.1.2.trans_le hOneB)
    · have hbOne : b < 1 := lt_of_not_ge hOneB
      have hbPos : 0 < b := D.hvfinal.1.trans hb
      have honeCap : (1 : ℝ) < (Real.sqrt Rmax * t)⁻¹ := by
        rw [one_lt_inv₀ haMax.1]
        exact haMax.2
      have hbDomain : b ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
        ⟨hbPos, hbOne.trans honeCap⟩
      have hvDomain : vfinal ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
        ⟨D.hvfinal.1, D.hvfinal.2.trans honeCap⟩
      have hstrict : lrSquareTarget Rmax b t <
          lrSquareTarget Rmax vfinal t := by
        change lrGShape (Real.sqrt Rmax * t) b <
          lrGShape (Real.sqrt Rmax * t) vfinal
        exact (strictAntiOn_lrGShape haMax) hvDomain hbDomain hb
      have hbTendsto : Tendsto (fun R : ℝ ↦ lrSquareTarget R b t) l
          (nhds (lrSquareTarget Rmax b t)) :=
        (continuous_lrSquareTarget_in_prefix b t).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have horder : ∀ᶠ R in l,
          lrSquareTarget R b t < lrPrefixEll R p := by
        apply hbTendsto.eventually_lt hellTendsto
        rw [D.hrootFinal]
        exact hstrict
      filter_upwards [hprefix, hrootSpec, horder] with R hR hs horderR
      have haR := D.prefix_shape_mem_Ioo hR
      have hrootDomain := D.root_mem_shape_domain hR
      have honeCapR : (1 : ℝ) < (Real.sqrt R * t)⁻¹ := by
        rw [one_lt_inv₀ haR.1]
        exact haR.2
      have hbDomainR : b ∈ Ioo (0 : ℝ) (Real.sqrt R * t)⁻¹ :=
        ⟨hbPos, hbOne.trans honeCapR⟩
      apply ((strictAntiOn_lrGShape haR).lt_iff_gt
        hbDomainR hrootDomain).mp
      change lrSquareTarget R b t < lrSquareTarget R (D.root R) t
      rw [← hs.2]
      exact horderR

/-- Relative continuity at the zero prefix follows from exact zero-prefix
identities; no asymptotic expansion is required. -/
theorem root_continuousWithinAt_zero
    (D : LRCanonicalTargetRootData p t Rmax vfinal) :
    ContinuousWithinAt D.root (Icc (0 : ℝ) Rmax) 0 := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Icc (0 : ℝ) Rmax)
  let u : ℝ := lrProbabilityToOdds p
  have hu : u ∈ Ioo (0 : ℝ) 1 := lrProbabilityToOdds_mem_Ioo D.hp
  have hself : ∀ᶠ R in l, R ∈ Icc (0 : ℝ) Rmax :=
    self_mem_nhdsWithin
  have hellTendsto : Tendsto (fun R : ℝ ↦ lrPrefixEll R p) l
      (nhds (lrPrefixEll 0 p)) :=
    (continuous_lrPrefixEll_in_prefix p).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  change Tendsto D.root l (nhds (D.root 0))
  rw [D.root_zero]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hself] with R hR
    by_cases hRzero : R = 0
    · simpa [hRzero, u] using ha
    · have hRpos : 0 < R := lt_of_le_of_ne hR.1 (Ne.symm hRzero)
      have hspec := D.root_spec ⟨hRpos, hR.2⟩
      exact ha.trans_le hspec.1.1
  · intro b hb
    have hbPos : 0 < b := hu.1.trans hb
    have hstrictZero : lrSquareTarget 0 b t < lrPrefixEll 0 p := by
      rw [lrSquareTarget_zero,
        lrPrefixEll_zero_eq_lrG_probabilityToOdds D.hp]
      exact strictAntiOn_lrG_pos hu.1 hbPos hb
    have hbTendsto : Tendsto (fun R : ℝ ↦ lrSquareTarget R b t) l
        (nhds (lrSquareTarget 0 b t)) :=
      (continuous_lrSquareTarget_in_prefix b t).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have horder : ∀ᶠ R in l,
        lrSquareTarget R b t < lrPrefixEll R p :=
      hbTendsto.eventually_lt hellTendsto hstrictZero
    filter_upwards [hself, horder] with R hR horderR
    by_cases hRzero : R = 0
    · simpa [hRzero, u] using hb
    · have hRpos : 0 < R := lt_of_le_of_ne hR.1 (Ne.symm hRzero)
      have hRIoc : R ∈ Ioc (0 : ℝ) Rmax := ⟨hRpos, hR.2⟩
      have hspec := D.root_spec hRIoc
      have haR := D.prefix_shape_mem_Ioo hRIoc
      have hrootDomain := D.root_mem_shape_domain hRIoc
      by_cases hOneB : (1 : ℝ) ≤ b
      · exact hspec.1.2.trans_le hOneB
      · have hbOne : b < 1 := lt_of_not_ge hOneB
        have honeCapR : (1 : ℝ) < (Real.sqrt R * t)⁻¹ := by
          rw [one_lt_inv₀ haR.1]
          exact haR.2
        have hbDomainR : b ∈ Ioo (0 : ℝ) (Real.sqrt R * t)⁻¹ :=
          ⟨hbPos, hbOne.trans honeCapR⟩
        apply ((strictAntiOn_lrGShape haR).lt_iff_gt
          hbDomainR hrootDomain).mp
        change lrSquareTarget R b t < lrSquareTarget R (D.root R) t
        rw [← hspec.2]
        exact horderR

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

/-- `topPhi` is locally `C^1` at every interior point.  The existing log
formula avoids any need for a smoothness theorem about `binEntropy`. -/
theorem contDiffAt_topPhi_one
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ 1 topPhi x := by
  have hplus : ContDiffAt ℝ 1 (fun y : ℝ ↦ 1 + y) x :=
    contDiffAt_const.add contDiffAt_id
  have hminus : ContDiffAt ℝ 1 (fun y : ℝ ↦ 1 - y) x :=
    contDiffAt_const.sub contDiffAt_id
  have hlogPlus : ContDiffAt ℝ 1 (fun y : ℝ ↦ Real.log (1 + y)) x :=
    hplus.log (by linarith [hx.1])
  have hlogMinus : ContDiffAt ℝ 1 (fun y : ℝ ↦ Real.log (1 - y)) x :=
    hminus.log (by linarith [hx.2])
  have hsmooth : ContDiffAt ℝ 1
      (fun y : ℝ ↦
        ((1 + y) * Real.log (1 + y) +
          (1 - y) * Real.log (1 - y)) / 2) x :=
    ((hplus.mul hlogPlus).add (hminus.mul hlogMinus)).div_const 2
  have heq : topPhi =ᶠ[nhds x]
      (fun y : ℝ ↦
        ((1 + y) * Real.log (1 + y) +
          (1 - y) * Real.log (1 - y)) / 2) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact topPhi_eq_log_formula hy
  exact hsmooth.congr_of_eventuallyEq heq

/-- The odds entropy quotient is locally `C^1` on its positive domain. -/
theorem contDiffAt_lrG_one {q : ℝ} (hq : 0 < q) :
    ContDiffAt ℝ 1 lrG q := by
  have hid : ContDiffAt ℝ 1 (fun y : ℝ ↦ y) q := contDiffAt_id
  have honePlus : ContDiffAt ℝ 1 (fun y : ℝ ↦ 1 + y) q :=
    contDiffAt_const.add hid
  have hinv : ContDiffAt ℝ 1 (fun y : ℝ ↦ y⁻¹) q :=
    hid.inv hq.ne'
  have hcoef : ContDiffAt ℝ 1 (fun y : ℝ ↦ 1 + y⁻¹) q :=
    contDiffAt_const.add hinv
  have hlogPlus : ContDiffAt ℝ 1 (fun y : ℝ ↦ Real.log (1 + y)) q :=
    honePlus.log (by linarith)
  have hlog : ContDiffAt ℝ 1 (fun y : ℝ ↦ Real.log y) q :=
    hid.log hq.ne'
  have hbody : lrG =
      (fun y : ℝ ↦ (1 + y⁻¹) * Real.log (1 + y) - Real.log y) := by
    funext y
    simp [lrG, one_div]
  rw [hbody]
  exact (hcoef.mul hlogPlus).sub hlog

/-- The exact target equation is locally `C^1` at every positive physical
point.  This is the main smoothness field required by Mathlib's IFT. -/
theorem contDiffAt_lrCanonicalTargetEquation_one
    {p t R v : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (lrCanonicalTargetEquation p t) (R, v) := by
  have hfst : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ z.1) (R, v) := contDiffAt_fst
  have hsnd : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ z.2) (R, v) := contDiffAt_snd
  have hsqrt : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ Real.sqrt z.1) (R, v) :=
    hfst.sqrt hR.1.ne'
  have hsqrtPos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hsqrtMem : Real.sqrt R ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, hsqrtLt⟩
  have hshape : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ Real.sqrt z.1 * t) (R, v) :=
    hsqrt.mul contDiffAt_const
  have hshapePos : 0 < Real.sqrt R * t := mul_pos hsqrtPos ht.1
  have hshapeLt : Real.sqrt R * t < 1 := by
    calc
      Real.sqrt R * t < 1 * t :=
        mul_lt_mul_of_pos_right hsqrtLt ht.1
      _ < 1 := by simpa using ht.2
  have hshapeMem : Real.sqrt R * t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, hshapeLt⟩
  have hscaledShape : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ Real.sqrt z.1 * t * z.2) (R, v) :=
    hshape.mul hsnd
  have hscaledShapePos : 0 < Real.sqrt R * t * v :=
    mul_pos hshapePos hv.1
  have hscaledShapeLt : Real.sqrt R * t * v < 1 := by
    calc
      Real.sqrt R * t * v = Real.sqrt R * (v * t) := by ring
      _ < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 * t := by
        simpa using (mul_lt_mul_of_pos_right hv.2 ht.1)
      _ < 1 := by simpa using ht.2
  have hscaledShapeMem :
      Real.sqrt R * t * v ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, hscaledShapeLt⟩
  have hGComp : ContDiffAt ℝ 1
      (lrG ∘ Prod.snd) (R, v) :=
    (contDiffAt_lrG_one hv.1).comp (R, v) hsnd
  have hG : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ lrG z.2) (R, v) :=
    by simpa only [Function.comp_apply] using hGComp
  have hphiShapeComp : ContDiffAt ℝ 1
      (topPhi ∘ (fun z : ℝ × ℝ ↦ Real.sqrt z.1 * t)) (R, v) :=
    (contDiffAt_topPhi_one hshapeMem).comp (R, v) hshape
  have hphiShape : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ topPhi (Real.sqrt z.1 * t)) (R, v) :=
    by simpa only [Function.comp_apply] using hphiShapeComp
  have hphiScaledShapeComp : ContDiffAt ℝ 1
      (topPhi ∘
        (fun z : ℝ × ℝ ↦ Real.sqrt z.1 * t * z.2)) (R, v) :=
    (contDiffAt_topPhi_one hscaledShapeMem).comp (R, v) hscaledShape
  have hphiScaledShape : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ topPhi (Real.sqrt z.1 * t * z.2))
        (R, v) :=
    by simpa only [Function.comp_apply] using hphiScaledShapeComp
  have htarget : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ lrSquareTarget z.1 z.2 t) (R, v) := by
    unfold lrSquareTarget lrGShape
    simpa only [mul_comm] using
      (hG.sub hphiShape).sub (hphiScaledShape.div hsnd hv.1.ne')
  have hphiSqrtComp : ContDiffAt ℝ 1
      (topPhi ∘ (fun z : ℝ × ℝ ↦ Real.sqrt z.1)) (R, v) :=
    (contDiffAt_topPhi_one hsqrtMem).comp (R, v) hsqrt
  have hphiSqrt : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ topPhi (Real.sqrt z.1)) (R, v) :=
    by simpa only [Function.comp_apply] using hphiSqrtComp
  have hprefixFirst : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦
        (1 - z.1) * Real.binEntropy p / p) (R, v) :=
    ((contDiffAt_const.sub hfst).mul contDiffAt_const).div_const p
  have hprefixSecond : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦
        4 * (z.1 * Real.log 2 - topPhi (Real.sqrt z.1)) * (1 - p))
        (R, v) :=
    ((contDiffAt_const.mul
      ((hfst.mul contDiffAt_const).sub hphiSqrt)).mul
        contDiffAt_const)
  have hprefix : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ ↦ lrPrefixEll z.1 p) (R, v) := by
    unfold lrPrefixEll
    exact hprefixFirst.add hprefixSecond
  unfold lrCanonicalTargetEquation
  exact htarget.sub hprefix

/-- Exact root-direction derivative, in a form suitable for comparing the
partial Fréchet derivative with a one-dimensional scalar map. -/
theorem hasDerivAt_lrCanonicalTargetEquation_snd
    {p t R v : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun q : ℝ ↦ lrCanonicalTargetEquation p t (R, q))
      (-(Real.log (1 + v) + lrL ((Real.sqrt R * t) * v)) / v ^ 2) v := by
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
  simpa [lrCanonicalTargetEquation, lrSquareTarget] using
    (hasDerivAt_lrGShape hv.1 ha0 hav).sub_const (lrPrefixEll R p)

/-- The `C^1` equation and its strictly negative root-direction derivative
assemble Mathlib's exact implicit-function hypothesis. -/
theorem isContDiffImplicitAt_lrCanonicalTargetEquation_one
    {p t R v : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    IsContDiffImplicitAt 1
      (lrCanonicalTargetEquation p t)
      (fderiv ℝ (lrCanonicalTargetEquation p t) (R, v))
      (R, v) := by
  let F : ℝ × ℝ → ℝ := lrCanonicalTargetEquation p t
  let F' : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ F (R, v)
  let c : ℝ :=
    -(Real.log (1 + v) + lrL ((Real.sqrt R * t) * v)) / v ^ 2
  have hC1 : ContDiffAt ℝ 1 F (R, v) := by
    simpa [F] using contDiffAt_lrCanonicalTargetEquation_one hR ht hv
  have hF : HasFDerivAt F F' (R, v) :=
    hC1.differentiableAt_one.hasFDerivAt
  have hright : HasFDerivAt (fun q : ℝ ↦ F (R, q))
      (F'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) v :=
    hF.comp v (hasFDerivAt_prodMk_right R v)
  have hscalar : HasDerivAt (fun q : ℝ ↦ F (R, q)) c v := by
    simpa [F, c] using
      hasDerivAt_lrCanonicalTargetEquation_snd hR ht hv
  have hpartial :
      F'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
        ContinuousLinearMap.toSpanSingleton ℝ c :=
    hright.unique hscalar
  have hcNeg : c < 0 := by
    have hneg := lrCanonicalTargetEquation_sndDeriv_neg
      (p := p) hR ht hv
    rw [hscalar.deriv] at hneg
    exact hneg
  have hc : c ≠ 0 := hcNeg.ne
  have hbijective : Function.Bijective
      (F'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    rw [hpartial]
    constructor
    · intro x y hxy
      have hmul : x * c = y * c := by
        simpa [ContinuousLinearMap.toSpanSingleton_apply] using hxy
      exact mul_right_cancel₀ hc hmul
    · intro y
      refine ⟨y / c, ?_⟩
      simp [ContinuousLinearMap.toSpanSingleton_apply, hc]
  exact {
    hasFDerivAt := hF
    contDiffAt := hC1
    bijective := hbijective
    ne_zero := by norm_num
  }

namespace LRCanonicalTargetRootData

variable {p t Rmax vfinal : ℝ}

/-- At every interior prefix, the Mathlib implicit branch agrees locally
with the canonical selector: both solve the same equation, and `lrGShape` is
strictly decreasing throughout their common physical neighborhood. -/
theorem root_differentiableAt
    (D : LRCanonicalTargetRootData p t Rmax vfinal)
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) Rmax) :
    DifferentiableAt ℝ D.root R := by
  have hRUnit : R ∈ Ioo (0 : ℝ) 1 :=
    ⟨hR.1, hR.2.trans D.hRmax.2⟩
  have hRPrefix : R ∈ Ioc (0 : ℝ) Rmax := ⟨hR.1, hR.2.le⟩
  have hv := D.root_physical hRPrefix
  let F : ℝ × ℝ → ℝ := lrCanonicalTargetEquation p t
  let a : ℝ × ℝ := (R, D.root R)
  let F' : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ F a
  have himplicit : IsContDiffImplicitAt 1 F F' a := by
    simpa [F, F', a] using
      isContDiffImplicitAt_lrCanonicalTargetEquation_one hRUnit D.ht hv
  let φ : ℝ → ℝ := himplicit.implicitFunction
  have hbaseZero : F a = 0 := by
    unfold F a lrCanonicalTargetEquation
    rw [D.root_target_eq hRPrefix]
    ring
  have hφBase : φ R = D.root R := by
    have hbase :=
      himplicit.eventually_implicitFunction_apply_eq.self_of_nhds
    exact hbase rfl
  have hφContinuous : ContinuousAt φ R := by
    exact himplicit.contDiffAt_implicitFunction.continuousAt
  have hφPhysical : ∀ᶠ x in nhds R, φ x ∈ Ioo (0 : ℝ) 1 := by
    have hmem : Ioo (0 : ℝ) 1 ∈ nhds (φ R) := by
      rw [hφBase]
      exact Ioo_mem_nhds hv.1 hv.2
    exact hφContinuous hmem
  have heq : D.root =ᶠ[nhds R] φ := by
    filter_upwards [Ioo_mem_nhds hR.1 hR.2, hφPhysical,
      himplicit.apply_implicitFunction] with x hx hφx hφEquation
    have hxUnit : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hx.1, hx.2.trans D.hRmax.2⟩
    have hxPrefix : x ∈ Ioc (0 : ℝ) Rmax := ⟨hx.1, hx.2.le⟩
    have hrootx := D.root_physical hxPrefix
    have hrootZero : F (x, D.root x) = 0 := by
      unfold F lrCanonicalTargetEquation
      rw [D.root_target_eq hxPrefix]
      ring
    have hφZero : F (x, φ x) = 0 := hφEquation.trans hbaseZero
    have hvalues :
        lrGShape (Real.sqrt x * t) (D.root x) =
          lrGShape (Real.sqrt x * t) (φ x) := by
      unfold F lrCanonicalTargetEquation lrSquareTarget at hrootZero hφZero
      linarith
    have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
    have hsqrtLt : Real.sqrt x < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hx.1.le).2 hxUnit.2
    have haShape : Real.sqrt x * t ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact mul_pos hsqrtPos D.ht.1
      · calc
          Real.sqrt x * t < 1 * t :=
            mul_lt_mul_of_pos_right hsqrtLt D.ht.1
          _ < 1 := by simpa using D.ht.2
    have honeCap : (1 : ℝ) < (Real.sqrt x * t)⁻¹ := by
      rw [one_lt_inv₀ haShape.1]
      exact haShape.2
    have hrootDomain :
        D.root x ∈ Ioo (0 : ℝ) (Real.sqrt x * t)⁻¹ :=
      ⟨hrootx.1, hrootx.2.trans honeCap⟩
    have hφDomain : φ x ∈ Ioo (0 : ℝ) (Real.sqrt x * t)⁻¹ :=
      ⟨hφx.1, hφx.2.trans honeCap⟩
    exact (strictAntiOn_lrGShape haShape).injOn
      hrootDomain hφDomain hvalues
  have hφDifferentiable : DifferentiableAt ℝ φ R :=
    himplicit.contDiffAt_implicitFunction.differentiableAt_one
  exact hφDifferentiable.congr_of_eventuallyEq heq

end LRCanonicalTargetRootData

/-- The canonical selector has all of the regularity required by the global
flow: one-sided continuity at both endpoints and differentiability at every
interior prefix. -/
theorem canonicalTargetRootRegularityTheorem :
    LRCanonicalTargetRootRegularityTheorem := by
  intro p t Rmax vfinal D
  exact ⟨D.root_continuousWithinAt_zero,
    D.root_continuousWithinAt_final,
    fun R hR ↦ D.root_differentiableAt hR⟩

/-- Strongest closure of the canonical target-root flow.  Once the pointwise
flow numerator theorem is known, the complete Courtade--Kumar statement
follows with no additional trajectory-regularity or endpoint hypothesis. -/
theorem courtadeKumar_of_targetFlow
    (hflow : LRTargetFlowNumeratorTheorem) :
    Statement :=
  courtadeKumar_of_targetFlow_and_canonicalRootRegularity
    hflow canonicalTargetRootRegularityTheorem

end CourtadeKumar
