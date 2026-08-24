import InformationTheory.CourtadeKumar.EntropyScalingSurplus

/-! Exact decomposition of the single-ray LR gap into a local gap and a
nonnegative scaling reserve. -/

open Set
open scoped NNReal

namespace CourtadeKumar

noncomputable def singleRayNatLocalGap (rho M r : ℝ) : ℝ :=
  (radialNatEntropy rho r M - radialNatEntropy 1 r M) -
    (lowerRayNatEnvelope rho M -
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2)

noncomputable def singleRayNatScalingReserve
    (rho c r z : ℝ) : ℝ :=
  (radialNatEntropy 1 r (c * z) - c * radialNatEntropy 1 r z) -
    (radialNatEntropy rho r (c * z) - c * radialNatEntropy rho r z)

/-- Convexity of entropy's scaling surplus makes the scaling reserve
nonnegative under every BSC contraction. -/
theorem singleRayNatScalingReserve_nonneg
    {rho c r z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Icc (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Icc (0 : ℝ) 1) :
    0 ≤ singleRayNatScalingReserve rho c r z := by
  unfold singleRayNatScalingReserve
  exact sub_nonneg.mpr
    (radialNatEntropy_scalingDeficit_contraction hc hrho hminus hplus)

/-- On the entropy-contact surface, the full LR target gap is exactly the
sum of the local two-point gap and the scaling reserve. -/
theorem singleRayNatGap_eq_local_add_scalingReserve
    {rho M r z c : ℝ}
    (hM : M = c * z)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    c * radialNatEntropy rho r z - lowerRayNatEnvelope rho M =
      singleRayNatLocalGap rho M r +
        singleRayNatScalingReserve rho c r z := by
  subst M
  unfold singleRayNatLocalGap singleRayNatScalingReserve
  linear_combination hcontact

/-- Consequently, nonnegativity of the decomposed reserve is sufficient for
the natural-unit LR inequality. -/
theorem singleRayNatGap_nonneg_of_decomposition
    {rho M r z c : ℝ}
    (hM : M = c * z)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2)
    (hdecomp : 0 ≤ singleRayNatLocalGap rho M r +
      singleRayNatScalingReserve rho c r z) :
    lowerRayNatEnvelope rho M ≤ c * radialNatEntropy rho r z := by
  rw [← sub_nonneg, singleRayNatGap_eq_local_add_scalingReserve hM hcontact]
  exact hdecomp

/-- Exact bit/nat bridge for the decomposed LR gap. -/
theorem singleRayBitGap_eq_natDecomposition
    {alpha : ℝ≥0} {M r z : ℝ}
    (hM : 0 < M) (hz : 0 < z)
    (hcontact : M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2) :
    M / z * radialTriangleChannelEntropy alpha r z -
        bellmanEnvelope (alpha : ℝ) M =
      (singleRayNatLocalGap (channelRho (alpha : ℝ)) M r +
        singleRayNatScalingReserve (channelRho (alpha : ℝ))
          (M / z) r z) / Real.log 2 := by
  let c : ℝ := M / z
  have hcz : M = c * z := by
    dsimp [c]
    field_simp [hz.ne']
  have hcontactNat : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope (channelRho (alpha : ℝ)) (M * (1 - r)) +
        lowerRayNatEnvelope (channelRho (alpha : ℝ)) (M * (1 + r))) / 2 := by
    have hminus := lowerRayNatEnvelope_eq_bellman
      (alpha : ℝ) (M * (1 - r))
    have hplus := lowerRayNatEnvelope_eq_bellman
      (alpha : ℝ) (M * (1 + r))
    rw [radialTriangleEntropy_eq_nat] at hcontact
    dsimp [c]
    rw [hminus, hplus]
    field_simp [log_two_ne_zero, hz.ne'] at hcontact ⊢
    linarith
  have hdecomp := singleRayNatGap_eq_local_add_scalingReserve
    hcz hcontactNat
  have henv := lowerRayNatEnvelope_eq_bellman (alpha : ℝ) M
  have henvDiv : bellmanEnvelope (alpha : ℝ) M =
      lowerRayNatEnvelope (channelRho (alpha : ℝ)) M / Real.log 2 := by
    rw [henv]
    field_simp [log_two_ne_zero]
  rw [radialTriangleChannelEntropy_eq_nat, henvDiv]
  dsimp [c] at hdecomp
  rw [← hdecomp]
  field_simp [log_two_ne_zero]

theorem singleRayScalarContact_of_natDecomposition
    (alpha : ℝ≥0)
    (hreserve : ∀ (M r z : ℝ),
      M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
      r ∈ Ioo (0 : ℝ) 1 →
      z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
      M / z * radialTriangleEntropy r z =
        (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
          bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 →
      0 ≤ singleRayNatLocalGap (channelRho (alpha : ℝ)) M r +
        singleRayNatScalingReserve (channelRho (alpha : ℝ)) (M / z) r z) :
    SingleRayScalarContactTheorem alpha := by
  intro M r z hM hr hz hcontact
  have hgap := hreserve M r z hM hr hz hcontact
  have hdiv : 0 ≤
      (singleRayNatLocalGap (channelRho (alpha : ℝ)) M r +
        singleRayNatScalingReserve (channelRho (alpha : ℝ)) (M / z) r z) /
          Real.log 2 :=
    div_nonneg hgap (Real.log_pos (by norm_num)).le
  rw [← singleRayBitGap_eq_natDecomposition hM.1 hz.1 hcontact] at hdiv
  exact sub_nonneg.mp hdiv

end CourtadeKumar
