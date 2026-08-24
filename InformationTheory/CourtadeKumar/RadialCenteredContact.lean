import InformationTheory.CourtadeKumar.RadialEulerClosedForm

/-! Explicit radial multiplier at the centered contact `z = 1/2`. -/

open Set

namespace CourtadeKumar

noncomputable def centeredRadialMultiplier (rho r : ℝ) : ℝ :=
  Real.log ((1 - rho ^ 2 * r ^ 2) / 4) /
    Real.log ((1 - r ^ 2) / 4)

theorem radialEulerRatio_centered
    {rho r : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    radialEulerRatio rho r (1 / 2) = centeredRadialMultiplier rho r := by
  have hminus : (1 - r) * (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  have hplus : (1 + r) * (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  have hrhor : 0 ≤ rho * r := mul_nonneg hrho.1 hr.1.le
  have hrhor_le : rho * r ≤ r := by
    simpa using mul_le_mul_of_nonneg_right hrho.2 hr.1.le
  have hrhor_lt : rho * r < 1 := hrhor_le.trans_lt hr.2
  have hRminus : (1 - rho * r) * (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith
  have hRplus : (1 + rho * r) * (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith
  have hdenArg : (1 - r ^ 2) / 4 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  have hdenLog : Real.log ((1 - r ^ 2) / 4) ≠ 0 :=
    (Real.log_neg hdenArg.1 hdenArg.2).ne
  have hD1 := radialEulerDefect_eq_log (c := (1 : ℝ)) (r := r) (z := (1 / 2 : ℝ))
    (by simpa using hminus) (by simpa using hplus)
  have hDrho := radialEulerDefect_eq_log hRminus hRplus
  unfold radialEulerRatio centeredRadialMultiplier
  rw [hDrho, hD1]
  rw [show (1 - (1 / 2 : ℝ)) ^ 2 - rho ^ 2 * r ^ 2 * (1 / 2 : ℝ) ^ 2 =
      (1 - rho ^ 2 * r ^ 2) / 4 by ring,
    show (1 - (1 / 2 : ℝ)) ^ 2 - 1 ^ 2 * r ^ 2 * (1 / 2 : ℝ) ^ 2 =
      (1 - r ^ 2) / 4 by ring]
  field_simp [hdenLog]

/-- Centered stationarity is exactly the explicit multiplier equation. -/
theorem radial_stationary_centered_iff
    {rho theta r : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    theta * radialEulerDefect 1 r (1 / 2) -
        radialEulerDefect rho r (1 / 2) = 0 ↔
      centeredRadialMultiplier rho r = theta := by
  have hminus : (1 - r) * (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  have hplus : (1 + r) * (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  rw [radial_stationary_iff_ratio hminus hplus,
    radialEulerRatio_centered hrho hr]

end CourtadeKumar
