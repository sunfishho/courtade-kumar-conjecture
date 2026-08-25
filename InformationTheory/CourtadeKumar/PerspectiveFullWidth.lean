import InformationTheory.CourtadeKumar.PerspectiveInteriorClassification
import InformationTheory.CourtadeKumar.RadialOneRay

/-! Direct primal-dual assembly on the singular perspective ray `r = 1`. -/

open Set
open scoped NNReal BigOperators

namespace CourtadeKumar

/-- Equality of uniform averages upgrades a pointwise inequality to
pointwise equality on the finite Boolean cube. -/
theorem eq_of_cubeAverage_eq_of_pointwise_le
    {n : ℕ} {f g : BitVec n → ℝ}
    (hfg : ∀ y, f y ≤ g y)
    (havg : cubeAverage n f = cubeAverage n g) :
    ∀ y, f y = g y := by
  have hsum : ∑ y, (g y - f y) = 0 := by
    unfold cubeAverage at havg
    rw [Finset.sum_sub_distrib]
    have hscale : 0 < ((2 ^ n : ℝ)⁻¹) := by positivity
    nlinarith
  have hnonneg : ∀ y, 0 ≤ g y - f y := fun y ↦ sub_nonneg.mpr (hfg y)
  have hzeroFun : (fun y ↦ g y - f y) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  intro y
  have hzero := congrFun hzeroFun y
  simp only [Pi.zero_apply] at hzero
  linarith

/-- The fields used by the manuscript's direct equality computation at
`r₀ = 1`.  There is intentionally no radial affine-minorant field: a finite
endpoint tangent need not exist. -/
structure FullWidthPhaseData
    (alpha : ℝ≥0) (M E0 : ℝ) where
  theta : ℝ
  c : ℝ → ℝ
  z : ℝ
  theta_nonneg : 0 ≤ theta
  z_pos : 0 < z
  contactProfile : RadialContactProfile alpha theta c
  radial_contact : c 1 = radialTriangleDifference alpha theta 1 z / z
  entropy_contact : E0 = M / z * radialTriangleEntropy 1 z
  lr_bound : bellmanEnvelope (alpha : ℝ) M ≤
    M / z * radialTriangleChannelEntropy alpha 1 z

/-- Endpoint geometry before inserting the LR scalar objective bound. -/
structure FullWidthGeometryData
    (alpha : ℝ≥0) (M E0 : ℝ) where
  theta : ℝ
  c : ℝ → ℝ
  z : ℝ
  alpha_interior : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)
  mean_interior : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)
  theta_nonneg : 0 ≤ theta
  contact_before_half : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)
  contactProfile : RadialContactProfile alpha theta c
  radial_contact : c 1 = radialTriangleDifference alpha theta 1 z / z
  entropy_contact : E0 = M / z * radialTriangleEntropy 1 z
  threshold_eq : E0 = bellmanEnvelope (alpha : ℝ) (2 * M) / 2

/-- The endpoint specialization of LR needed by the direct full-width
phase. -/
def FullWidthLRTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M E0 : ℝ) (h : FullWidthGeometryData alpha M E0),
    bellmanEnvelope (alpha : ℝ) M ≤
      M / h.z * radialTriangleChannelEntropy alpha 1 h.z

noncomputable def FullWidthGeometryData.toPhaseData
    {alpha : ℝ≥0} {M E0 : ℝ}
    (hlr : FullWidthLRTheorem alpha)
    (h : FullWidthGeometryData alpha M E0) :
    FullWidthPhaseData alpha M E0 where
  theta := h.theta
  c := h.c
  z := h.z
  theta_nonneg := h.theta_nonneg
  z_pos := h.contact_before_half.1
  contactProfile := h.contactProfile
  radial_contact := h.radial_contact
  entropy_contact := h.entropy_contact
  lr_bound := hlr M E0 h

/-- The canonical singular-ray contact realizes all endpoint geometry once
the entropy level is matched. -/
noncomputable def canonicalFullWidthGeometryData
    {alpha : ℝ≥0} {M E0 z : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hentropy : E0 / M = radialEntropyRatio 1 z)
    (hthreshold : E0 = bellmanEnvelope (alpha : ℝ) (2 * M) / 2) :
    FullWidthGeometryData alpha M E0 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let theta : ℝ := radialEulerLogRatio rho 1 z
  let c : ℝ → ℝ := canonicalRadialProfile alpha theta halpha
    (radialEulerLogRatio_mem_Ioo_oneRay
      (by
        dsimp [rho]
        unfold channelRho
        constructor <;> linarith [halpha.1, halpha.2]) hz)
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rho]
    unfold channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have htheta : theta ∈ Ioo (0 : ℝ) 1 :=
    radialEulerLogRatio_mem_Ioo_oneRay hrho hz
  have hzphys : z ∈ Ioo (0 : ℝ) (1 + (1 : ℝ))⁻¹ := by
    norm_num at hz ⊢
    exact hz
  have hspec := canonicalRadialContactZ_spec halpha htheta
    (show (0 : ℝ) < 1 by norm_num)
  have hcanonical :
      canonicalRadialContactZ alpha theta halpha htheta 1 = z :=
    (existsUnique_radialEulerLogRatio_eq
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
      htheta (by norm_num)).unique
        ⟨hspec.1, hspec.2⟩ ⟨hzphys, rfl⟩
  refine {
    theta := theta
    c := c
    z := z
    alpha_interior := halpha
    mean_interior := hM
    theta_nonneg := htheta.1.le
    contact_before_half := hz
    contactProfile := canonicalRadialProfile_contactProfile halpha htheta
    radial_contact := ?_
    entropy_contact := ?_
    threshold_eq := hthreshold }
  · dsimp [c]
    rw [canonicalRadialProfile, if_pos (by norm_num), hcanonical]
  · calc
      E0 = M * (E0 / M) := by field_simp [hM.1.ne']
      _ = M * radialEntropyRatio 1 z := by rw [hentropy]
      _ = M / z * radialTriangleEntropy 1 z := by
        unfold radialEntropyRatio
        ring

/-- A positive interior full-width mean selects its singular-ray entropy
contact canonically. -/
theorem exists_canonicalFullWidthGeometryData
    {alpha : ℝ≥0} {M E0 : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hthreshold : E0 = bellmanEnvelope (alpha : ℝ) (2 * M) / 2) :
    Nonempty (FullWidthGeometryData alpha M E0) := by
  have h2M : 2 * M ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hM.1, hM.2]
  have hE0 : 0 < E0 := by
    rw [hthreshold]
    exact div_pos (bellmanEnvelope_pos_of_mem_Ioo halpha h2M) (by norm_num)
  have hlevel : 0 < E0 / M := div_pos hE0 hM.1
  obtain ⟨z, hz, hzeq⟩ :=
    (existsUnique_radialEntropyRatio_oneRay_eq_before_half hlevel).exists
  exact ⟨canonicalFullWidthGeometryData
    halpha hM hz hzeq.symm hthreshold⟩

lemma orderedTriangleChannelEntropy_half_fullWidth
    (alpha : ℝ≥0) :
    orderedTriangleChannelEntropy alpha (1 / 2) (1 / 2) =
      bellmanEnvelope (alpha : ℝ) (1 / 2) := by
  have hsym : binaryEntropyBits (1 - (alpha : ℝ)) =
      binaryEntropyBits (alpha : ℝ) := binaryEntropyBits_one_sub _
  unfold orderedTriangleChannelEntropy bellmanEnvelope channelRho channelS
    bellmanLambda
  rw [show (1 / 2 : ℝ) - (1 - 2 * (alpha : ℝ)) * (1 / 2) =
      (alpha : ℝ) by ring,
    show (1 / 2 : ℝ) + (1 - 2 * (alpha : ℝ)) * (1 / 2) =
      1 - (alpha : ℝ) by ring,
    hsym]
  have hhalf : binaryEntropyBits (1 / 2) = 1 := by
    unfold binaryEntropyBits
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.binEntropy_two_inv]
    field_simp [log_two_ne_zero]
  rw [hhalf]
  unfold channelS channelRho
  ring

/-- Direct weak duality along `r = 1`, followed by the manuscript's exact
contact equalities, proves the full-width Bellman case without a global
finite-slope support. -/
theorem orderedTriangle_fullWidthBellmanStep_of_phaseData
    {alpha : ℝ≥0} {n : ℕ} {M U : BitVec n → ℝ}
    (hdomain : ∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y)
    (hmean : cubeAverage n U = cubeAverage n M)
    (hentropy :
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2 ≤
      cubeAverage n (fun y ↦ orderedTriangleEntropy (M y) (U y)))
    (h : FullWidthPhaseData alpha (cubeAverage n M)
      ((bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2)) :
    bellmanEnvelope (alpha : ℝ) (cubeAverage n M) ≤
      cubeAverage n (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) := by
  have hpointEq : ∀ y, U y = M y :=
    eq_of_cubeAverage_eq_of_pointwise_le (fun y ↦ (hdomain y).2.1) hmean
  let e : BitVec n → ℝ := fun y ↦ orderedTriangleEntropy (M y) (U y)
  let j : BitVec n → ℝ :=
    fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)
  have hpoint : ∀ y, h.theta * e y + h.c 1 * M y ≤ j y := by
    intro y
    have hm0 : 0 ≤ M y := by rw [← hpointEq y]; exact (hdomain y).1
    have hmcap : M y ≤ 1 / (1 + (1 : ℝ)) := by
      have hy := (hdomain y).2.2
      rw [hpointEq y] at hy
      norm_num
      linarith
    have hr := radialPerspectiveLowerBound_of_contactProfile h.contactProfile
      1 (M y) (by norm_num) hm0 hmcap
    rw [radialTriangleDifference_eq_ordered, one_mul] at hr
    dsimp [e, j]
    rw [hpointEq y]
    linarith
  have havg := cubeAverage_mono hpoint
  have hlinear :
      cubeAverage n (fun y ↦ h.theta * e y + h.c 1 * M y) =
        h.theta * cubeAverage n e + h.c 1 * cubeAverage n M := by
    rw [cubeAverage_add, cubeAverage_const_mul, cubeAverage_const_mul]
  rw [hlinear] at havg
  have hscaled := mul_le_mul_of_nonneg_left hentropy h.theta_nonneg
  dsimp [e, j] at havg hscaled
  have hdual :
      h.theta *
          ((bellmanEnvelope (alpha : ℝ)
              (cubeAverage n M - cubeAverage n U) +
            bellmanEnvelope (alpha : ℝ)
              (cubeAverage n M + cubeAverage n U)) / 2) +
          h.c 1 * cubeAverage n M ≤
        cubeAverage n
          (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) := by
    linarith
  have hz : h.z ≠ 0 := h.z_pos.ne'
  have hcontactIdentity :
      h.theta *
          ((bellmanEnvelope (alpha : ℝ)
              (cubeAverage n M - cubeAverage n U) +
            bellmanEnvelope (alpha : ℝ)
              (cubeAverage n M + cubeAverage n U)) / 2) +
          h.c 1 * cubeAverage n M =
        cubeAverage n M / h.z *
          radialTriangleChannelEntropy alpha 1 h.z := by
    calc
      h.theta *
            ((bellmanEnvelope (alpha : ℝ)
                (cubeAverage n M - cubeAverage n U) +
              bellmanEnvelope (alpha : ℝ)
                (cubeAverage n M + cubeAverage n U)) / 2) +
          h.c 1 * cubeAverage n M =
          h.theta * (cubeAverage n M / h.z *
              radialTriangleEntropy 1 h.z) +
            h.c 1 * cubeAverage n M :=
        congrArg (fun x : ℝ ↦ h.theta * x + h.c 1 * cubeAverage n M)
          h.entropy_contact
      _ = h.theta * (cubeAverage n M / h.z *
              radialTriangleEntropy 1 h.z) +
            (radialTriangleDifference alpha h.theta 1 h.z / h.z) *
              cubeAverage n M := by rw [h.radial_contact]
      _ = cubeAverage n M / h.z *
          radialTriangleChannelEntropy alpha 1 h.z := by
        unfold radialTriangleDifference
        field_simp [hz]
        ring
  rw [hcontactIdentity] at hdual
  exact h.lr_bound.trans hdual

/-- The singular endpoint is now reduced exactly to its LR specialization.
The two hard endpoints `M = 0` and `M = 1/2` are direct identities. -/
theorem fullWidthBellmanStep_of_LR
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hlr : FullWidthLRTheorem alpha) :
    OrderedTriangleLowerHalfFullWidthBellmanStep alpha := by
  intro n M U hdomain hhalf hmean hentropy
  have hpointEq : ∀ y, U y = M y :=
    eq_of_cubeAverage_eq_of_pointwise_le (fun y ↦ (hdomain y).2.1) hmean
  obtain ⟨_, _, _, hMIcc⟩ := orderedTriangle_cubeAverage_bounds hdomain
  by_cases hMzero : cubeAverage n M = 0
  · rw [hMzero, bellmanEnvelope_zero]
    have hnonneg : ∀ y, 0 ≤
        orderedTriangleChannelEntropy alpha (M y) (U y) := by
      intro y
      exact orderedTriangleChannelEntropy_nonneg halpha.2.le
        (hdomain y).1 (hdomain y).2.1 (hdomain y).2.2
    simpa using cubeAverage_mono
      (f := fun _ ↦ (0 : ℝ))
      (g := fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y))
      hnonneg
  by_cases hMhalf : cubeAverage n M = 1 / 2
  · have hMcap : ∀ y, M y ≤ (1 / 2 : ℝ) := by
      intro y
      have hy := (hdomain y).2.2
      rw [hpointEq y] at hy
      linarith
    have hMpoint : ∀ y, M y = (fun _ ↦ (1 / 2 : ℝ)) y := by
      apply eq_of_cubeAverage_eq_of_pointwise_le hMcap
      rw [cubeAverage_const, hMhalf]
    have hj : cubeAverage n
        (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) =
        orderedTriangleChannelEntropy alpha (1 / 2) (1 / 2) := by
      calc
        cubeAverage n
            (fun y ↦ orderedTriangleChannelEntropy alpha (M y) (U y)) =
            cubeAverage n (fun _ ↦
              orderedTriangleChannelEntropy alpha (1 / 2) (1 / 2)) := by
              apply cubeAverage_congr
              intro y
              rw [hpointEq y, hMpoint y]
        _ = orderedTriangleChannelEntropy alpha (1 / 2) (1 / 2) :=
          cubeAverage_const n _
    rw [hMhalf, hj, orderedTriangleChannelEntropy_half_fullWidth]
  · have hM : cubeAverage n M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) := by
      constructor
      · exact lt_of_le_of_ne hMIcc.1 (Ne.symm hMzero)
      · exact lt_of_le_of_ne hhalf hMhalf
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    have hthreshold : E0 =
        bellmanEnvelope (alpha : ℝ) (2 * cubeAverage n M) / 2 := by
      dsimp [E0]
      rw [hmean, sub_self, bellmanEnvelope_zero]
      rw [show cubeAverage n M + cubeAverage n M =
          2 * cubeAverage n M by ring]
      ring
    obtain ⟨hgeometry⟩ :=
      exists_canonicalFullWidthGeometryData halpha hM hthreshold
    exact orderedTriangle_fullWidthBellmanStep_of_phaseData
      hdomain hmean hentropy (hgeometry.toPhaseData hlr)

/-- For every interior BSC, the two LR interfaces now assemble the complete
lower-half Bellman step: the existing perspective/TOP proof handles strict
width, and the singular specialization handles full width directly. -/
theorem lowerHalfBellmanStep_of_singleRayLR
    {alpha : ℝ≥0}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hlr : SingleRayLRTheorem alpha)
    (hlrOne : FullWidthLRTheorem alpha) :
    OrderedTriangleLowerHalfBellmanStep alpha :=
  orderedTriangleLowerHalfBellmanStep_of_strictAffineSupport_and_fullWidth
    alpha (lowerHalfStrictAffineSupport_of_interior_LR halpha hlr)
      (fullWidthBellmanStep_of_LR halpha hlrOne)

/-- Exact endpoint phase output required from the remaining scalar contact
selection and LR proof. -/
def OrderedTriangleLowerHalfFullWidthPhaseTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (M U : BitVec n → ℝ),
    (∀ y, 0 ≤ U y ∧ U y ≤ M y ∧ U y ≤ 1 - M y) →
    cubeAverage n M ≤ 1 / 2 →
    cubeAverage n U = cubeAverage n M →
    let E0 :=
      (bellmanEnvelope (alpha : ℝ) (cubeAverage n M - cubeAverage n U) +
        bellmanEnvelope (alpha : ℝ) (cubeAverage n M + cubeAverage n U)) / 2
    Nonempty (FullWidthPhaseData alpha (cubeAverage n M) E0)

theorem fullWidthBellmanStep_of_phase
    (alpha : ℝ≥0)
    (hphase : OrderedTriangleLowerHalfFullWidthPhaseTheorem alpha) :
    OrderedTriangleLowerHalfFullWidthBellmanStep alpha := by
  intro n M U hdomain hhalf hmean hentropy
  obtain ⟨h⟩ := hphase n M U hdomain hhalf hmean
  exact orderedTriangle_fullWidthBellmanStep_of_phaseData
    hdomain hmean hentropy h

end CourtadeKumar
