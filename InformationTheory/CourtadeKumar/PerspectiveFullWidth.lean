import InformationTheory.CourtadeKumar.PerspectiveInteriorClassification

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
