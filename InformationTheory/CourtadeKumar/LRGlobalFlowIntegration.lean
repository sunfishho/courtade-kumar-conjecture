import InformationTheory.CourtadeKumar.ChannelEndpoints
import InformationTheory.CourtadeKumar.LRFullFlowReduced
import InformationTheory.CourtadeKumar.LRFullWidthEndpointClosure

/-!
# Global integration of the LR target-root flow

This module isolates the genuinely global analytic input still needed after
the pointwise LR numerator inequality has been proved.  The existing
development supplies a unique physical target root at every positive channel
prefix and computes the derivative of the reserve along every differentiable
root curve.  Beyond the pointwise determinant theorem, exactly one global
input remains explicit here:

1. a single choice of the unique target roots which is regular on the whole
   closed prefix interval.

The singular full-width (`r = 1`) LR endpoint is not a second analytic
input: `LRFullWidthEndpointClosure` derives it from the open-ray scalar
theorem by continuity and uniqueness of the entropy contact.

`LRRegularTargetRootTrajectory` records exactly that regularity.  No
existence of such a trajectory is assumed silently: the quantified interface
`LRRegularTargetRootTrajectoryTheorem` below is a named remaining theorem.
From it and the pointwise numerator theorem, this file proves:

* monotonicity of the squared-coordinate reserve from `R = 0`;
* nonnegativity of the reserve at the final target root;
* the automatic/root contradiction which gives the LR objective inequality;
* the open single-ray scalar contact theorem;
* the full-width continuity closure; and
* the final closed-ray and Courtade--Kumar reduction.

The extra `reserve_continuousOn` field is deliberately explicit for now.  It
should ultimately be derived from `root_continuousOn` and continuity of the
closed formulas; keeping it visible makes the endpoint hypothesis honest
while the root-regularity construction is developed.
-/

open Filter Set
open scoped NNReal

namespace CourtadeKumar

/-- The pointwise analytic theorem needed by global flow integration.  The
determinant/interval work is designed to instantiate precisely this interface.
-/
def LRTargetFlowNumeratorTheorem : Prop :=
  ∀ (R p v t : ℝ),
    R ∈ Ioo (0 : ℝ) 1 →
    p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) →
    v ∈ Ioo (0 : ℝ) 1 →
    t ∈ Ioo (0 : ℝ) 1 →
    lrPrefixEll R p = lrSquareTarget R v t →
    0 ≤ lrFlowNumeratorP R p v t

/-- A globally regular choice of the unique physical target roots on the
closed channel-prefix interval.  At `R = 0` the target root is the input odds;
at every positive prefix it is the physical root of the exact target equation.
-/
structure LRRegularTargetRootTrajectory
    (p t Rmax vfinal : ℝ) where
  root : ℝ → ℝ
  root_zero : root 0 = lrProbabilityToOdds p
  root_final : root Rmax = vfinal
  root_physical : ∀ R ∈ Ioc (0 : ℝ) Rmax, root R ∈ Ioo (0 : ℝ) 1
  target_eq : ∀ R ∈ Ioc (0 : ℝ) Rmax,
    lrPrefixEll R p = lrSquareTarget R (root R) t
  root_continuousOn : ContinuousOn root (Icc (0 : ℝ) Rmax)
  root_differentiableAt : ∀ R ∈ Ioo (0 : ℝ) Rmax,
    DifferentiableAt ℝ root R
  reserve_continuousOn : ContinuousOn
    (fun R : ℝ ↦
      lrSquareReserve R (lrProbabilityToOdds p) (root R) t)
    (Icc (0 : ℝ) Rmax)

/-- The exact global regularity theorem still to be proved for the canonical
unique-root selector.  Its hypotheses are the final strict physical root and
the final target equation; prefix existence and uniqueness are already proved
in `LRPrefixPhysicality`.
-/
def LRRegularTargetRootTrajectoryTheorem : Prop :=
  ∀ (p t Rmax vfinal : ℝ),
    p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    t ∈ Ioo (0 : ℝ) 1 →
    Rmax ∈ Ioo (0 : ℝ) 1 →
    vfinal ∈ Ioo (0 : ℝ) 1 →
    lrProbabilityToOdds p ≤ vfinal →
    lrPrefixEll Rmax p = lrSquareTarget Rmax vfinal t →
    Nonempty (LRRegularTargetRootTrajectory p t Rmax vfinal)

namespace LRRegularTargetRootTrajectory

variable {p t Rmax vfinal : ℝ}

/-- The target equation on the open prefix interval is an eventual equality
in the exact form required by implicit differentiation.
-/
theorem eventuallyEq_squareTarget_squareObjective
    (trajectory : LRRegularTargetRootTrajectory p t Rmax vfinal)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1)
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) Rmax) :
    (fun y : ℝ ↦ lrSquareTarget y (trajectory.root y) t) =ᶠ[nhds R]
      (fun y : ℝ ↦ lrSquareObjective y (lrProbabilityToOdds p)) := by
  filter_upwards [Ioo_mem_nhds hR.1 hR.2] with y hy
  have hyUnit : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hy.1, hy.2.trans hRmax.2⟩
  calc
    lrSquareTarget y (trajectory.root y) t = lrPrefixEll y p :=
      (trajectory.target_eq y ⟨hy.1, hy.2.le⟩).symm
    _ = lrObjectiveTarget (Real.sqrt y) (lrProbabilityToOdds p) :=
      lrPrefixEll_eq_lrObjectiveTarget hyUnit hp
    _ = lrSquareObjective y (lrProbabilityToOdds p) :=
      (lrSquareObjective_eq hyUnit).symm

/-- The squared-coordinate reserve has the exact elementary base value.
Unlike the `rho`-coordinate formula, this identity is nonsingular at `R = 0`.
-/
@[simp] theorem lrSquareReserve_zero_sameRoot (u t : ℝ) :
    lrSquareReserve 0 u u t = 0 := by
  simp [lrSquareReserve, lrQSquare, lrPhiPerspective,
    lrNormalizedEnergy, topPhi_zero]

/-- Along a regular target-root trajectory, the complete pointwise numerator
theorem gives an exact derivative together with its sign.
-/
theorem hasDerivAt_reserve_and_nonneg
    (hflow : LRTargetFlowNumeratorTheorem)
    (trajectory : LRRegularTargetRootTrajectory p t Rmax vfinal)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1)
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) Rmax) :
    let d :=
      lrFlowNumerator R (lrProbabilityToOdds p) (trajectory.root R) t /
        (lrFlowB R (trajectory.root R) t * (1 - R) ^ 2 * t ^ 2)
    HasDerivAt
        (fun y : ℝ ↦
          lrSquareReserve y (lrProbabilityToOdds p) (trajectory.root y) t)
        d R ∧ 0 ≤ d := by
  dsimp only
  have hRUnit : R ∈ Ioo (0 : ℝ) 1 :=
    ⟨hR.1, hR.2.trans hRmax.2⟩
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hv := trajectory.root_physical R ⟨hR.1, hR.2.le⟩
  have hvt : trajectory.root R * t < 1 := calc
    trajectory.root R * t < 1 * t :=
      mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have htarget := trajectory.target_eq R ⟨hR.1, hR.2.le⟩
  have hroot :
      lrGShape (Real.sqrt R * t) (trajectory.root R) =
        lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) := by
    calc
      lrGShape (Real.sqrt R * t) (trajectory.root R) =
          lrSquareTarget R (trajectory.root R) t := rfl
      _ = lrPrefixEll R p := htarget.symm
      _ = lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) :=
        lrPrefixEll_eq_lrObjectiveTarget hRUnit hp
  have hvfun : HasDerivAt trajectory.root (deriv trajectory.root R) R :=
    (trajectory.root_differentiableAt R hR).hasDerivAt
  have hderiv := hasDerivAt_lrReserve_exactFlow hRUnit hu.1 hv.1 ht hvt
    rfl hvfun hroot
      (trajectory.eventuallyEq_squareTarget_squareObjective hp hRmax hR)
  have hpOdds : lrFlowP (lrProbabilityToOdds p) = p := by
    simpa [lrFlowP, lrOddsToProbability] using
      lrOddsToProbability_probabilityToOdds
        (show p < 1 from hp.2.trans (by norm_num))
  have hnumP : 0 ≤ lrFlowNumeratorP R p (trajectory.root R) t :=
    hflow R p (trajectory.root R) t hRUnit
      ⟨hp.1, hp.2.le⟩ hv ht htarget
  have hnum :
      0 ≤ lrFlowNumerator R (lrProbabilityToOdds p)
        (trajectory.root R) t := by
    rw [lrFlowNumerator_eq_p, hpOdds]
    exact hnumP
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hRUnit.1.le).2 hRUnit.2
  have hshape : Real.sqrt R * trajectory.root R * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (trajectory.root R * t) <
          1 * (trajectory.root R * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R (trajectory.root R) t :=
    lrFlowB_pos hv.1 ht.1.le hshape
  have hden :
      0 < lrFlowB R (trajectory.root R) t * (1 - R) ^ 2 * t ^ 2 :=
    mul_pos (mul_pos hB (sq_pos_of_pos (sub_pos.mpr hRUnit.2)))
      (sq_pos_of_pos ht.1)
  exact ⟨hderiv, div_nonneg hnum hden.le⟩

/-- The reserve is monotone on the entire closed prefix interval.  Endpoint
continuity, rather than a derivative at the singular base point, is exactly
what allows the usual mean-value theorem to include `R = 0`.
-/
theorem reserve_monotoneOn
    (hflow : LRTargetFlowNumeratorTheorem)
    (trajectory : LRRegularTargetRootTrajectory p t Rmax vfinal)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1) :
    MonotoneOn
      (fun R : ℝ ↦
        lrSquareReserve R (lrProbabilityToOdds p) (trajectory.root R) t)
      (Icc (0 : ℝ) Rmax) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc (0 : ℝ) Rmax)
  · exact trajectory.reserve_continuousOn
  · intro R hR
    rw [interior_Icc] at hR
    exact (trajectory.hasDerivAt_reserve_and_nonneg
      hflow hp ht hRmax hR).1.hasDerivWithinAt
  · intro R hR
    rw [interior_Icc] at hR
    exact (trajectory.hasDerivAt_reserve_and_nonneg
      hflow hp ht hRmax hR).2

/-- Integration from the exact zero-channel base proves the final target-root
reserve.  This is the first theorem in the flow development that actually
crosses the whole channel-prefix interval.
-/
theorem reserve_nonneg_at_final
    (hflow : LRTargetFlowNumeratorTheorem)
    (trajectory : LRRegularTargetRootTrajectory p t Rmax vfinal)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrSquareReserve Rmax (lrProbabilityToOdds p) vfinal t := by
  have hmono := trajectory.reserve_monotoneOn hflow hp ht hRmax
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) Rmax :=
    ⟨le_rfl, hRmax.1.le⟩
  have hfinal : Rmax ∈ Icc (0 : ℝ) Rmax :=
    ⟨hRmax.1.le, le_rfl⟩
  have hle := hmono hzero hfinal hRmax.1.le
  change
    lrSquareReserve 0 (lrProbabilityToOdds p) (trajectory.root 0) t ≤
      lrSquareReserve Rmax (lrProbabilityToOdds p)
        (trajectory.root Rmax) t at hle
  rw [trajectory.root_zero, trajectory.root_final] at hle
  simpa using hle

end LRRegularTargetRootTrajectory

/-- The integrated reserve closes the manuscript's automatic/root split.
If the desired LR objective inequality failed at the actual entropy-contact
odds `v`, strict decrease of `G_a` would put the target root strictly to its
left.  The nonnegative reserve gives the opposite ordering at uncontracted
shape, contradicting the entropy-contact equation.
-/
theorem lrObjectiveTarget_le_of_targetFlow_and_regularTrajectories
    (hflow : LRTargetFlowNumeratorTheorem)
    (htrajectory : LRRegularTargetRootTrajectoryTheorem)
    {p t Rmax v : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hRmax : Rmax ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1)
    (hcontact : lrGShape t v =
      lrEntropyTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) t) :
    lrObjectiveTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) ≤
      lrGShape (Real.sqrt Rmax * t) v := by
  by_contra hnot
  have hfail :
      lrGShape (Real.sqrt Rmax * t) v <
        lrObjectiveTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) :=
    lt_of_not_ge hnot
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hsqrtPos : 0 < Real.sqrt Rmax := Real.sqrt_pos.2 hRmax.1
  have hsqrtLt : Real.sqrt Rmax < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hRmax.1.le).2 hRmax.2
  have ha : Real.sqrt Rmax * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hsqrtPos ht.1
    · calc
        Real.sqrt Rmax * t < 1 * t :=
          mul_lt_mul_of_pos_right hsqrtLt ht.1
        _ < 1 := by simpa using ht.2
  have honeCap : (1 : ℝ) < (Real.sqrt Rmax * t)⁻¹ := by
    rw [one_lt_inv₀ ha.1]
    exact ha.2
  have hvChannelDomain :
      v ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
    ⟨hv.1, hv.2.trans honeCap⟩
  have honeChannelDomain :
      (1 : ℝ) ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
    ⟨by norm_num, honeCap⟩
  have hupper :
      lrGShape (Real.sqrt Rmax * t) 1 ≤
        lrObjectiveTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) := by
    have hstrict := (strictAntiOn_lrGShape ha)
      hvChannelDomain honeChannelDomain hv.2
    exact (hstrict.trans hfail).le
  have htSq : t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hsqrtMul : Real.sqrt (Rmax * t ^ 2) = Real.sqrt Rmax * t := by
    rw [Real.sqrt_mul hRmax.1.le, Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
  have hlowerPrefix := lrPrefix_lowerBracket hp htSq hRmax
  have hlower :
      lrObjectiveTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) ≤
        lrGShape (Real.sqrt Rmax * t) (lrProbabilityToOdds p) := by
    rw [lrPrefixEll_eq_lrObjectiveTarget hRmax hp,
      hsqrtMul] at hlowerPrefix
    exact hlowerPrefix
  obtain ⟨w, ⟨hw, hroot⟩, _⟩ :=
    existsUnique_lrGShape_eq_of_bracket ha hu hupper hlower
  have hwChannelDomain :
      w ∈ Ioo (0 : ℝ) (Real.sqrt Rmax * t)⁻¹ :=
    ⟨hu.1.trans_le hw.1, hw.2.trans_lt honeCap⟩
  have hwlt : w < v := by
    by_contra hnotwv
    have hvw : v ≤ w := le_of_not_gt hnotwv
    have hanti := (strictAntiOn_lrGShape ha).antitoneOn
      hvChannelDomain hwChannelDomain hvw
    linarith
  have hwIoo : w ∈ Ioo (0 : ℝ) 1 :=
    ⟨hu.1.trans_le hw.1, hwlt.trans hv.2⟩
  have hrootFinal :
      lrPrefixEll Rmax p = lrSquareTarget Rmax w t := by
    calc
      lrPrefixEll Rmax p =
          lrObjectiveTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) :=
        lrPrefixEll_eq_lrObjectiveTarget hRmax hp
      _ = lrGShape (Real.sqrt Rmax * t) w := hroot.symm
      _ = lrSquareTarget Rmax w t := rfl
  obtain ⟨trajectory⟩ := htrajectory p t Rmax w hp ht hRmax
    hwIoo hw.1 hrootFinal
  have hreserveSquare :=
    trajectory.reserve_nonneg_at_final hflow hp ht hRmax
  have hreserve :
      0 ≤ lrReserve (Real.sqrt Rmax) (lrProbabilityToOdds p) w t := by
    rw [← lrSquareReserve_eq_lrReserve hRmax]
    exact hreserveSquare
  have hQ :
      lrKappa (Real.sqrt Rmax) (lrProbabilityToOdds p) ≤
        lrQClosed (Real.sqrt Rmax) (lrProbabilityToOdds p) w t := by
    exact sub_nonneg.mp (by simpa [lrReserve] using hreserve)
  have hrho : Real.sqrt Rmax ∈ Ioo (0 : ℝ) 1 :=
    ⟨hsqrtPos, hsqrtLt⟩
  have hwEntropy :
      lrGShape t w ≤
        lrEntropyTarget (Real.sqrt Rmax) (lrProbabilityToOdds p) t :=
    (lr_contactAtTarget_iff_Q hrho hu.1 hwIoo.1 ht.1 hroot).2 hQ
  have htInv : (1 : ℝ) < t⁻¹ := by
    rw [one_lt_inv₀ ht.1]
    exact ht.2
  have hwShapeDomain : w ∈ Ioo (0 : ℝ) t⁻¹ :=
    ⟨hwIoo.1, hwIoo.2.trans htInv⟩
  have hvShapeDomain : v ∈ Ioo (0 : ℝ) t⁻¹ :=
    ⟨hv.1, hv.2.trans htInv⟩
  have hstrict := (strictAntiOn_lrGShape ht)
    hwShapeDomain hvShapeDomain hwlt
  linarith

/-- The pointwise numerator theorem plus global target-root regularity prove
the complete open single-ray scalar contact theorem for every interior BSC.
-/
theorem singleRayScalarContact_of_targetFlow_and_regularTrajectories
    (hflow : LRTargetFlowNumeratorTheorem)
    (htrajectory : LRRegularTargetRootTrajectoryTheorem)
    (alpha : ℝ≥0) :
    SingleRayScalarContactTheorem alpha := by
  intro halpha M r z hM hr hz hcontact
  let rho : ℝ := channelRho (alpha : ℝ)
  let u : ℝ := lrProbabilityToOdds M
  let v : ℝ := lrProbabilityToOdds z
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hu : u ∈ Ioo (0 : ℝ) 1 := by
    dsimp [u]
    exact lrProbabilityToOdds_mem_Ioo hM
  have hv : v ∈ Ioo (0 : ℝ) 1 := by
    dsimp [v]
    exact lrProbabilityToOdds_mem_Ioo hz
  have hMback : lrOddsToProbability u = M := by
    dsimp [u]
    exact lrOddsToProbability_probabilityToOdds
      (hM.2.trans (by norm_num))
  have hzback : lrOddsToProbability v = z := by
    dsimp [v]
    exact lrOddsToProbability_probabilityToOdds
      (hz.2.trans (by norm_num))
  have hcontactNat := singleRayNatContact_of_bitContact hz.1 hcontact
  have hcontactOdds :
      lrGShape r v = lrEntropyTarget rho u r := by
    apply (singleRayNatContact_iff_lrEntropyContact
      hrho hu ⟨hv.1, hv.2.le⟩ hr).mp
    simpa [rho, hMback, hzback] using hcontactNat
  have hRmax : rho ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hrho.1, hrho.2]
  have hsqrtRho : Real.sqrt (rho ^ 2) = rho := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrho.1]
  have hcontactRmax :
      lrGShape r v =
        lrEntropyTarget (Real.sqrt (rho ^ 2))
          (lrProbabilityToOdds M) r := by
    rw [hsqrtRho]
    simpa [u] using hcontactOdds
  have htarget :=
    lrObjectiveTarget_le_of_targetFlow_and_regularTrajectories
      hflow htrajectory hM hr hRmax hv hcontactRmax
  rw [hsqrtRho] at htarget
  have hnatOdds :=
    (singleRayNatLR_iff_lrObjectiveTarget
      hrho hu ⟨hv.1, hv.2.le⟩ hr).2 htarget
  have hnat :
      lowerRayNatEnvelope rho M ≤
        M / z * radialNatEntropy rho r z := by
    simpa [hMback, hzback] using hnatOdds
  have hscaled :
      Real.log 2 * bellmanEnvelope (alpha : ℝ) M ≤
        M / z * radialNatEntropy rho r z := by
    rw [← lowerRayNatEnvelope_eq_bellman (alpha : ℝ) M]
    simpa [rho] using hnat
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [radialTriangleChannelEntropy_eq_nat]
  calc
    bellmanEnvelope (alpha : ℝ) M ≤
        (M / z * radialNatEntropy rho r z) / Real.log 2 := by
      apply (le_div_iff₀ hlog).2
      simpa [mul_comm] using hscaled
    _ = M / z *
        (radialNatEntropy (channelRho (alpha : ℝ)) r z /
          Real.log 2) := by
      dsimp [rho]
      ring

/-- The only extra ingredient needed to pass from the open scalar theorem to
the manuscript's closed-ray theorem is the singular full-width LR statement.
The `r = 1` branch is assembled canonically from its scalar contact equation.
-/
theorem singleRayClosedScalarContact_of_scalarContact_and_fullWidth
    (alpha : ℝ≥0)
    (hscalar : SingleRayScalarContactTheorem alpha)
    (hfull : FullWidthLRTheorem alpha) :
    SingleRayClosedScalarContactTheorem alpha := by
  intro halpha M r z hM hr hz hcontact
  by_cases hrOne : r = 1
  · subst r
    let E0 : ℝ := M / z * radialTriangleEntropy 1 z
    have hthreshold :
        E0 = bellmanEnvelope (alpha : ℝ) (2 * M) / 2 := by
      calc
        E0 =
            (bellmanEnvelope (alpha : ℝ) (M * (1 - 1)) +
              bellmanEnvelope (alpha : ℝ) (M * (1 + 1))) / 2 :=
          hcontact
        _ = bellmanEnvelope (alpha : ℝ) (2 * M) / 2 := by
          rw [show M * (1 - (1 : ℝ)) = 0 by ring,
            show M * (1 + (1 : ℝ)) = 2 * M by ring,
            bellmanEnvelope_zero]
          ring
    have hratio : E0 / M = radialEntropyRatio 1 z := by
      dsimp [E0]
      unfold radialEntropyRatio
      field_simp [hM.1.ne', hz.1.ne']
    let geometry := canonicalFullWidthGeometryData
      halpha hM hz hratio hthreshold
    exact hfull M E0 geometry
  · exact hscalar halpha M r z hM
      ⟨hr.1, lt_of_le_of_ne hr.2 hrOne⟩ hz hcontact

/-- Backward-compatible end-to-end closure with the full-width theorem kept
as an explicit argument.  The stronger theorem below constructs this argument
from the open scalar theorem automatically. -/
theorem courtadeKumar_of_targetFlow_regularTrajectories_and_fullWidth
    (hflow : LRTargetFlowNumeratorTheorem)
    (htrajectory : LRRegularTargetRootTrajectoryTheorem)
    (hfull : ∀ (alpha : ℝ≥0),
      (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
        FullWidthLRTheorem alpha) :
    Statement := by
  apply courtadeKumar_of_closedScalarContact
  intro alpha halpha
  exact singleRayClosedScalarContact_of_scalarContact_and_fullWidth alpha
    (singleRayScalarContact_of_targetFlow_and_regularTrajectories
      hflow htrajectory alpha)
    (hfull alpha halpha)

/-- Strongest end-to-end closure of the present LR flow architecture.  The
open scalar theorem supplies the singular full-width endpoint by continuity,
so target-root regularity is the only global input beyond the pointwise flow
numerator theorem. -/
theorem courtadeKumar_of_targetFlow_regularTrajectories
    (hflow : LRTargetFlowNumeratorTheorem)
    (htrajectory : LRRegularTargetRootTrajectoryTheorem) :
    Statement := by
  apply courtadeKumar_of_targetFlow_regularTrajectories_and_fullWidth
    hflow htrajectory
  intro alpha _halpha
  exact fullWidthLR_of_singleRayScalarContact alpha
    (singleRayScalarContact_of_targetFlow_and_regularTrajectories
      hflow htrajectory alpha)

end CourtadeKumar
