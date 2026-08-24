import InformationTheory.CourtadeKumar.RadialMidpointLogRatio
import InformationTheory.CourtadeKumar.RadialPerspectiveUnimodal

/-! Positivity of the midpoint gradient on the lower radial branch. -/

open Set

namespace CourtadeKumar

theorem scaledNatEntropyDirectionalFirst_radial_m_eq_log_gap
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    scaledNatEntropyDirectionalFirst c z (r * z) 1 0 0 =
      (Real.log (radialEulerLogArg c r z) -
        Real.log (radialEulerMassArg c r z)) / 2 := by
  let qminus : ℝ := (1 - c * r) * z
  let qplus : ℝ := (1 + c * r) * z
  have hXprod : (1 - qminus) * (1 - qplus) =
      radialEulerLogArg c r z := by
    dsimp [qminus, qplus]
    unfold radialEulerLogArg
    ring
  have hYprod : qminus * qplus = radialEulerMassArg c r z := by
    dsimp [qminus, qplus]
    unfold radialEulerMassArg
    ring
  have hlogX : Real.log (radialEulerLogArg c r z) =
      Real.log (1 - qminus) + Real.log (1 - qplus) := by
    rw [← hXprod, Real.log_mul (by linarith [hminus.2])
      (by linarith [hplus.2])]
  have hlogY : Real.log (radialEulerMassArg c r z) =
      Real.log qminus + Real.log qplus := by
    rw [← hYprod, Real.log_mul hminus.1.ne' hplus.1.ne']
  unfold scaledNatEntropyDirectionalFirst natEntropySlope
  simp only [zero_mul, mul_zero, sub_zero, add_zero]
  rw [hlogX, hlogY]
  dsimp [qminus, qplus]
  ring

theorem naturalTriangleKm_radial_eq_log_gap
    {rho theta r z : ℝ}
    (hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    naturalTriangleKm rho theta z (r * z) =
      ((Real.log (radialEulerLogArg rho r z) -
          Real.log (radialEulerMassArg rho r z)) -
        theta * (Real.log (radialEulerLogArg 1 r z) -
          Real.log (radialEulerMassArg 1 r z))) / 2 := by
  unfold naturalTriangleKm naturalTriangleDirectionalFirst
  rw [scaledNatEntropyDirectionalFirst_radial_m_eq_log_gap hRminus hRplus]
  rw [scaledNatEntropyDirectionalFirst_radial_m_eq_log_gap
    (c := (1 : ℝ)) (by simpa using hminus) (by simpa using hplus)]
  ring

theorem naturalTriangleKm_pos_of_log_ratio_stationary
    {rho theta r z : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (1 / 2 : ℝ) (1 + r)⁻¹)
    (htheta : theta = Real.log (radialEulerLogArg rho r z) /
      Real.log (radialEulerLogArg 1 r z)) :
    0 < naturalTriangleKm rho theta z (r * z) := by
  have h1r : 0 < 1 + r := by linarith [hr.1]
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
      _ = 1 := inv_mul_cancel₀ h1r.ne'
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical
      (show rho ∈ Icc (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2.le⟩) hr
      ⟨(lt_trans (by norm_num) hz.1), hz.2⟩
  have hformula := naturalTriangleKm_radial_eq_log_gap
    (theta := theta) hRminus hRplus hminus hplus
  have hratio := radialEulerMidpointLogRatio_rho_lt_one
    hrho hr.1 ⟨hz.1, hz.2.trans (by
      have : (1 + r)⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀ (by linarith [hr.1])
      exact this)⟩ hupper
  let XR : ℝ := radialEulerLogArg rho r z
  let X1 : ℝ := radialEulerLogArg 1 r z
  let YR : ℝ := radialEulerMassArg rho r z
  let Y1 : ℝ := radialEulerMassArg 1 r z
  have hXargs := radialEulerLogArg_order_physical
    (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
    hr.1 (lt_trans (by norm_num) hz.1) hupper
  have hXR : XR ∈ Ioo (0 : ℝ) 1 :=
    ⟨hXargs.2.1.1, hXargs.2.1.2.trans (by linarith [hz.1])⟩
  have hX1 : X1 ∈ Ioo (0 : ℝ) 1 :=
    ⟨hXargs.1.1, hXargs.1.2.trans (by linarith [hz.1])⟩
  have hYR : YR ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [YR]
      rw [radialEulerMassArg_eq_logArg_add]
      nlinarith [hXargs.2.1.1, hz.1]
    · unfold YR radialEulerMassArg
      have hnonneg : 0 ≤ rho ^ 2 * r ^ 2 * z ^ 2 := by positivity
      have hz1 : z < 1 := hz.2.trans
        (inv_lt_one_of_one_lt₀ (by linarith [hr.1]))
      have hzplus : 0 < 1 + z := by linarith [hz.1]
      have hzsq : z ^ 2 < 1 := by
        nlinarith [mul_pos (sub_pos.2 hz1) hzplus]
      nlinarith
  have hY1 : Y1 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [Y1]
      rw [radialEulerMassArg_eq_logArg_add]
      nlinarith [hXargs.1.1, hz.1]
    · unfold Y1 radialEulerMassArg
      have hnonneg : 0 ≤ (1 : ℝ) ^ 2 * r ^ 2 * z ^ 2 := by positivity
      have hz1 : z < 1 := hz.2.trans
        (inv_lt_one_of_one_lt₀ (by linarith [hr.1]))
      have hzplus : 0 < 1 + z := by linarith [hz.1]
      have hzsq : z ^ 2 < 1 := by
        nlinarith [mul_pos (sub_pos.2 hz1) hzplus]
      nlinarith
  have hlogXR : Real.log XR < 0 := Real.log_neg hXR.1 hXR.2
  have hlogX1 : Real.log X1 < 0 := Real.log_neg hX1.1 hX1.2
  have hlogYR : Real.log YR < 0 := Real.log_neg hYR.1 hYR.2
  have hlogY1 : Real.log Y1 < 0 := Real.log_neg hY1.1 hY1.2
  change Real.log XR / Real.log YR < Real.log X1 / Real.log Y1 at hratio
  have hprod : 0 < Real.log YR * Real.log Y1 :=
    mul_pos_of_neg_of_neg hlogYR hlogY1
  have hcross0 := mul_lt_mul_of_pos_right hratio hprod
  have hleft : (Real.log XR / Real.log YR) *
      (Real.log YR * Real.log Y1) = Real.log XR * Real.log Y1 := by
    field_simp [hlogYR.ne]
  have hright : (Real.log X1 / Real.log Y1) *
      (Real.log YR * Real.log Y1) = Real.log X1 * Real.log YR := by
    field_simp [hlogY1.ne]
  rw [hleft, hright] at hcross0
  rw [hformula, htheta]
  change 0 < ((Real.log XR - Real.log YR) -
    Real.log XR / Real.log X1 * (Real.log X1 - Real.log Y1)) / 2
  have hnum : Real.log XR * Real.log Y1 -
      Real.log X1 * Real.log YR < 0 := by linarith
  have heq : ((Real.log XR - Real.log YR) -
      Real.log XR / Real.log X1 * (Real.log X1 - Real.log Y1)) / 2 =
      (Real.log XR * Real.log Y1 - Real.log X1 * Real.log YR) /
        (2 * Real.log X1) := by
    field_simp [hlogX1.ne]
    ring
  rw [heq]
  exact div_pos_of_neg_of_neg hnum (mul_neg_of_pos_of_neg (by norm_num) hlogX1)

end CourtadeKumar
