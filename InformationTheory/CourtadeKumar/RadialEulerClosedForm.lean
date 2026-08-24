import InformationTheory.CourtadeKumar.RadialDerivative

/-! Closed logarithmic form and positivity of the radial Euler defect. -/

open Set

namespace CourtadeKumar

/-- The Euler defect is the logarithm of the product of the two remaining
probability masses. -/
theorem radialEulerDefect_eq_log
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerDefect c r z =
      -(1 / 2 : ℝ) *
        Real.log ((1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2) := by
  have hm : 1 - (1 - c * r) * z ≠ 0 := by linarith [hminus.2]
  have hp : 1 - (1 + c * r) * z ≠ 0 := by linarith [hplus.2]
  calc
    radialEulerDefect c r z = -(1 / 2 : ℝ) *
        (Real.log (1 - (1 - c * r) * z) +
          Real.log (1 - (1 + c * r) * z)) := by
      unfold radialEulerDefect radialNatEntropy radialNatEntropyDeriv
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
        Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      simp only [Real.negMulLog_eq_neg]
      ring
    _ = -(1 / 2 : ℝ) * Real.log
        ((1 - (1 - c * r) * z) * (1 - (1 + c * r) * z)) := by
      rw [Real.log_mul hm hp]
    _ = -(1 / 2 : ℝ) *
        Real.log ((1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2) := by
      congr 2
      ring

theorem radialEulerDefect_pos
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    0 < radialEulerDefect c r z := by
  rw [radialEulerDefect_eq_log hminus hplus]
  let A : ℝ := 1 - (1 - c * r) * z
  let B : ℝ := 1 - (1 + c * r) * z
  have hA : A ∈ Ioo (0 : ℝ) 1 := by
    dsimp [A]
    constructor <;> linarith [hminus.1, hminus.2]
  have hB : B ∈ Ioo (0 : ℝ) 1 := by
    dsimp [B]
    constructor <;> linarith [hplus.1, hplus.2]
  have hprod : A * B ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨mul_pos hA.1 hB.1,
      mul_lt_one_of_nonneg_of_lt_one_left hA.1.le hA.2 hB.2.le⟩
  have harg : (1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2 = A * B := by
    dsimp [A, B]
    ring
  rw [harg]
  have hlog : Real.log (A * B) < 0 := Real.log_neg hprod.1 hprod.2
  nlinarith

/-- Ratio whose level sets are exactly radial stationary contacts. -/
noncomputable def radialEulerRatio (rho r z : ℝ) : ℝ :=
  radialEulerDefect rho r z / radialEulerDefect 1 r z

theorem radial_stationary_iff_ratio
    {rho theta r z : ℝ}
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    theta * radialEulerDefect 1 r z - radialEulerDefect rho r z = 0 ↔
      radialEulerRatio rho r z = theta := by
  have hD : radialEulerDefect 1 r z ≠ 0 :=
    (radialEulerDefect_pos (by simpa using hminus) (by simpa using hplus)).ne'
  unfold radialEulerRatio
  constructor
  · intro h
    apply (div_eq_iff hD).2
    linarith
  · intro h
    have := (div_eq_iff hD).1 h
    linarith

end CourtadeKumar
