import InformationTheory.CourtadeKumar.SingleRayStrictReduction

/-! Explicit algebraic forms of the strict single-ray contact and gap. -/

namespace CourtadeKumar

@[simp] theorem radialNatEntropy_zero_shape (c z : ℝ) :
    radialNatEntropy c 0 z = Real.binEntropy z := by
  simp [radialNatEntropy]

/-- Averaging the natural Bellman envelope over a radial pair separates its
entropy and quadratic contributions. -/
theorem average_lowerRayNatEnvelope_radial (rho M r : ℝ) :
    (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2 =
      topS rho * radialNatEntropy 1 r M +
        4 * topEll rho * M * (1 - M * (1 + r ^ 2)) := by
  unfold lowerRayNatEnvelope radialNatEntropy
  ring

/-- The local term is channel entropy gain minus the Bellman curvature
required across the same two-point split. -/
theorem singleRayNatLocalGap_explicit (rho M r : ℝ) :
    singleRayNatLocalGap rho M r =
      (radialNatEntropy rho r M - radialNatEntropy 1 r M) -
        (topS rho * (Real.binEntropy M - radialNatEntropy 1 r M) +
          4 * topEll rho * M ^ 2 * r ^ 2) := by
  unfold singleRayNatLocalGap
  rw [average_lowerRayNatEnvelope_radial]
  unfold lowerRayNatEnvelope
  ring

/-- The entropy-contact equation in separated natural units. -/
theorem singleRayNatContact_explicit
    {rho M r z c : ℝ}
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    c * radialNatEntropy 1 r z =
      topS rho * radialNatEntropy 1 r M +
        4 * topEll rho * M * (1 - M * (1 + r ^ 2)) := by
  rw [hcontact, average_lowerRayNatEnvelope_radial]

/-- On contact, the full natural LR gap has a compact entropy-gain form. -/
theorem singleRayNatGap_explicit_of_contact
    {rho M r z c : ℝ}
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    c * radialNatEntropy rho r z - lowerRayNatEnvelope rho M =
      c * (radialNatEntropy rho r z - radialNatEntropy 1 r z) -
        topS rho * (Real.binEntropy M - radialNatEntropy 1 r M) -
          4 * topEll rho * M ^ 2 * r ^ 2 := by
  have hexplicit := singleRayNatContact_explicit hcontact
  unfold lowerRayNatEnvelope
  linear_combination hexplicit

noncomputable def singleRayContactDenom (M r : ℝ) : ℝ :=
  1 - M * (1 + r ^ 2)

noncomputable def singleRayEntropyResidual
    (rho M r z c : ℝ) : ℝ :=
  singleRayContactDenom M r *
      c * (radialNatEntropy rho r z - radialNatEntropy 1 r z) -
    singleRayContactDenom M r * topS rho *
      (Real.binEntropy M - radialNatEntropy 1 r M) -
    M * r ^ 2 *
      (c * radialNatEntropy 1 r z -
        topS rho * radialNatEntropy 1 r M)

@[simp] theorem singleRayNatLocalGap_zero_shape (rho M : ℝ) :
    singleRayNatLocalGap rho M 0 = 0 := by
  rw [singleRayNatLocalGap_explicit]
  simp

@[simp] theorem singleRayEntropyResidual_zero_shape
    (rho M z c : ℝ) :
    singleRayEntropyResidual rho M 0 z c = 0 := by
  simp [singleRayEntropyResidual]

theorem continuous_singleRayEntropyResidual
    (rho M z c : ℝ) :
    Continuous (singleRayEntropyResidual rho M · z c) := by
  unfold singleRayEntropyResidual singleRayContactDenom radialNatEntropy
  fun_prop

theorem singleRayContactDenom_pos
    {M r : ℝ} (hM : M ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 < singleRayContactDenom M r := by
  unfold singleRayContactDenom
  have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
  have hfactor : 1 + r ^ 2 < 2 := by linarith
  have hprod : M * (1 + r ^ 2) < (1 / 2) * 2 := by
    calc
      M * (1 + r ^ 2) < (1 / 2) * (1 + r ^ 2) :=
        mul_lt_mul_of_pos_right hM.2 (by positivity)
      _ < (1 / 2) * 2 :=
        mul_lt_mul_of_pos_left hfactor (by norm_num)
  nlinarith

/-- Multiplying the LR gap by its positive contact denominator removes the
Bellman energy coefficient and leaves a pure-entropy residual. -/
theorem singleRayContactDenom_mul_gap_eq_entropyResidual
    {rho M r z c : ℝ}
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2) :
    singleRayContactDenom M r *
        (c * radialNatEntropy rho r z - lowerRayNatEnvelope rho M) =
      singleRayEntropyResidual rho M r z c := by
  have hexplicit := singleRayNatContact_explicit hcontact
  rw [singleRayNatGap_explicit_of_contact hcontact]
  unfold singleRayEntropyResidual singleRayContactDenom
  linear_combination M * r ^ 2 * hexplicit

/-- Nonnegativity of the pure-entropy residual is sufficient for the
natural LR target on the physical strict domain. -/
theorem singleRayNatGap_nonneg_of_entropyResidual
    {rho M r z c : ℝ}
    (hM : M ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : c * radialNatEntropy 1 r z =
      (lowerRayNatEnvelope rho (M * (1 - r)) +
        lowerRayNatEnvelope rho (M * (1 + r))) / 2)
    (hresidual : 0 ≤ singleRayEntropyResidual rho M r z c) :
    lowerRayNatEnvelope rho M ≤ c * radialNatEntropy rho r z := by
  rw [← singleRayContactDenom_mul_gap_eq_entropyResidual hcontact] at hresidual
  exact sub_nonneg.mp
    ((mul_nonneg_iff_of_pos_left (singleRayContactDenom_pos hM hr)).mp hresidual)

end CourtadeKumar
