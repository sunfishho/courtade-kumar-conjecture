import InformationTheory.CourtadeKumar.RadialCenteredContact

/-! Derivative and cross-numerator of the closed radial Euler ratio. -/

open Set

namespace CourtadeKumar

noncomputable def radialEulerLogArg (c r z : ℝ) : ℝ :=
  (1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2

noncomputable def radialEulerLog (c r z : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (radialEulerLogArg c r z)

noncomputable def radialEulerLogDeriv (c r z : ℝ) : ℝ :=
  (1 - z + c ^ 2 * r ^ 2 * z) / radialEulerLogArg c r z

theorem radialEulerDefect_eq_logFunction
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerDefect c r z = radialEulerLog c r z := by
  rw [radialEulerDefect_eq_log hminus hplus]
  rfl

theorem hasDerivAt_radialEulerLog
    {c r z : ℝ} (harg : radialEulerLogArg c r z ≠ 0) :
    HasDerivAt (radialEulerLog c r)
      (radialEulerLogDeriv c r z) z := by
  have hinner : HasDerivAt (radialEulerLogArg c r)
      (-2 * (1 - z) - 2 * c ^ 2 * r ^ 2 * z) z := by
    unfold radialEulerLogArg
    convert (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).pow 2).sub
      (((hasDerivAt_id z).pow 2).const_mul (c ^ 2 * r ^ 2)) using 1 <;>
      simp [id_eq] <;> ring
  have hlog := (Real.hasDerivAt_log harg).comp z hinner
  unfold radialEulerLog radialEulerLogDeriv
  convert hlog.const_mul (-(1 / 2 : ℝ)) using 1
  field_simp [harg]
  ring

noncomputable def radialEulerLogRatio (rho r z : ℝ) : ℝ :=
  radialEulerLog rho r z / radialEulerLog 1 r z

noncomputable def radialEulerRatioCrossNumerator (rho r z : ℝ) : ℝ :=
  radialEulerLogDeriv rho r z * radialEulerLog 1 r z -
    radialEulerLog rho r z * radialEulerLogDeriv 1 r z

theorem hasDerivAt_radialEulerLogRatio
    {rho r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0)
    (hden : radialEulerLog 1 r z ≠ 0) :
    HasDerivAt (radialEulerLogRatio rho r)
      (radialEulerRatioCrossNumerator rho r z /
        radialEulerLog 1 r z ^ 2) z := by
  have hR := hasDerivAt_radialEulerLog hargR
  have h1 := hasDerivAt_radialEulerLog harg1
  unfold radialEulerLogRatio radialEulerRatioCrossNumerator
  exact hR.div h1 hden

theorem radialEulerRatio_eq_logRatio
    {rho r z : ℝ}
    (hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerRatio rho r z = radialEulerLogRatio rho r z := by
  unfold radialEulerRatio radialEulerLogRatio
  rw [radialEulerDefect_eq_logFunction hRminus hRplus]
  have h1 := radialEulerDefect_eq_logFunction
    (c := (1 : ℝ)) (r := r) (z := z)
    (by simpa using hminus) (by simpa using hplus)
  rw [h1]

theorem radialEulerLog_pos
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    0 < radialEulerLog c r z := by
  rw [← radialEulerDefect_eq_logFunction hminus hplus]
  exact radialEulerDefect_pos hminus hplus

/-- The sign of the derivative of the radial Euler ratio is exactly the sign
of its cross-numerator. This is the scalar sign certificate needed by the
perspective argument. -/
theorem deriv_radialEulerLogRatio_lt_zero_iff
    {rho r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0)
    (hden : radialEulerLog 1 r z ≠ 0) :
    deriv (radialEulerLogRatio rho r) z < 0 ↔
      radialEulerRatioCrossNumerator rho r z < 0 := by
  rw [(hasDerivAt_radialEulerLogRatio hargR harg1 hden).deriv]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (div_nonneg (le_of_not_gt hn) (sq_nonneg _))) h
  · intro h
    exact div_neg_of_neg_of_pos h (sq_pos_of_ne_zero hden)

/-- A negative cross-numerator on the interior of a convex domain makes the
radial Euler ratio strictly decreasing on the whole domain. -/
theorem strictAntiOn_radialEulerLogRatio_of_crossNumerator_neg
    {rho r : ℝ} {D : Set ℝ}
    (hD : Convex ℝ D)
    (hargR : ∀ z ∈ D, radialEulerLogArg rho r z ≠ 0)
    (harg1 : ∀ z ∈ D, radialEulerLogArg 1 r z ≠ 0)
    (hden : ∀ z ∈ D, radialEulerLog 1 r z ≠ 0)
    (hcross : ∀ z ∈ interior D,
      radialEulerRatioCrossNumerator rho r z < 0) :
    StrictAntiOn (radialEulerLogRatio rho r) D := by
  apply strictAntiOn_of_deriv_neg hD
  · intro z hz
    exact (hasDerivAt_radialEulerLogRatio
      (hargR z hz) (harg1 z hz) (hden z hz)).continuousAt.continuousWithinAt
  · intro z hz
    rw [deriv_radialEulerLogRatio_lt_zero_iff
      (hargR z (interior_subset hz))
      (harg1 z (interior_subset hz))
      (hden z (interior_subset hz))]
    exact hcross z hz

end CourtadeKumar
