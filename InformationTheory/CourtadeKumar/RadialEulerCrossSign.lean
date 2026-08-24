import InformationTheory.CourtadeKumar.RadialLogFraction

/-! Transfer of the logarithmic-fraction monotonicity to the Euler core. -/

open Set

namespace CourtadeKumar

theorem log_cross_neg_of_lt
    {q x y : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) q)
    (hy : y ∈ Ioo (0 : ℝ) q)
    (hxy : x < y) :
    y * (q - x) * Real.log y - x * (q - y) * Real.log x < 0 := by
  have hmono := radialLogFraction_strictMonoOn hq hx hy hxy
  unfold radialLogFraction at hmono
  have hqx : 0 < q - x := sub_pos.2 hx.2
  have hqy : 0 < q - y := sub_pos.2 hy.2
  rw [div_lt_div_iff₀ hqx hqy] at hmono
  simp only [Real.negMulLog_def] at hmono
  nlinarith

theorem radialEulerSlopeNumerator_eq_arg_gap_div
    {c r z : ℝ} (hz : z ≠ 0) :
    radialEulerSlopeNumerator c r z =
      ((1 - z) - radialEulerLogArg c r z) / z := by
  unfold radialEulerSlopeNumerator radialEulerLogArg
  field_simp [hz]
  ring

theorem radialEulerCrossCore_eq_logCross_div
    {rho r z : ℝ} (hz : z ≠ 0) :
    radialEulerCrossCore rho r z =
      (radialEulerLogArg rho r z *
          ((1 - z) - radialEulerLogArg 1 r z) *
          Real.log (radialEulerLogArg rho r z) -
        radialEulerLogArg 1 r z *
          ((1 - z) - radialEulerLogArg rho r z) *
          Real.log (radialEulerLogArg 1 r z)) / z := by
  unfold radialEulerCrossCore
  rw [radialEulerSlopeNumerator_eq_arg_gap_div hz,
    radialEulerSlopeNumerator_eq_arg_gap_div hz]
  field_simp [hz]

/-- Abstract physical-domain version of the radial cross sign. The remaining
work is only to verify the four displayed order hypotheses from the triangle
parameters. -/
theorem radialEulerCrossCore_neg_of_arg_order
    {rho r z : ℝ}
    (hz : 0 < z)
    (hq : 1 - z ∈ Ioo (0 : ℝ) 1)
    (harg1 : radialEulerLogArg 1 r z ∈ Ioo (0 : ℝ) (1 - z))
    (hargR : radialEulerLogArg rho r z ∈ Ioo (0 : ℝ) (1 - z))
    (horder : radialEulerLogArg 1 r z < radialEulerLogArg rho r z) :
    radialEulerCrossCore rho r z < 0 := by
  rw [radialEulerCrossCore_eq_logCross_div hz.ne']
  exact div_neg_of_neg_of_pos
    (log_cross_neg_of_lt hq harg1 hargR horder) hz

/-- The two Euler-log arguments have the exact order required by the scalar
monotonicity lemma throughout the open radial cell. -/
theorem radialEulerLogArg_order_physical
    {rho r z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : 0 < r)
    (hz : 0 < z)
    (hupper : (1 + r) * z < 1) :
    radialEulerLogArg 1 r z ∈ Ioo (0 : ℝ) (1 - z) ∧
      radialEulerLogArg rho r z ∈ Ioo (0 : ℝ) (1 - z) ∧
      radialEulerLogArg 1 r z < radialEulerLogArg rho r z := by
  have hrz : 0 < r * z := mul_pos hr hz
  have hq0 : 0 < 1 - z := by nlinarith
  have hq1 : 1 - z < 1 := by linarith
  have hgap : 0 < 1 - z - r * z := by nlinarith [hupper]
  have hsum : 0 < 1 - z + r * z := by nlinarith
  have harg1pos : 0 < radialEulerLogArg 1 r z := by
    unfold radialEulerLogArg
    nlinarith [mul_pos hgap hsum]
  have hqsq : (1 - z) ^ 2 < 1 - z := by
    nlinarith [mul_pos hq0 (sub_pos.2 hq1)]
  have harg1lt : radialEulerLogArg 1 r z < 1 - z := by
    unfold radialEulerLogArg
    nlinarith [sq_nonneg (r * z)]
  have hrhoplus : 0 < 1 + rho := by linarith [hrho.1]
  have hrhosq : rho ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.2 hrho.2) hrhoplus]
  have hspread : 0 < r ^ 2 * z ^ 2 :=
    mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hz)
  have horder : radialEulerLogArg 1 r z < radialEulerLogArg rho r z := by
    unfold radialEulerLogArg
    nlinarith [mul_pos (sub_pos.2 hrhosq) hspread]
  have hargRpos : 0 < radialEulerLogArg rho r z :=
    harg1pos.trans horder
  have hargRlt : radialEulerLogArg rho r z < 1 - z := by
    unfold radialEulerLogArg
    nlinarith [mul_nonneg (sq_nonneg rho)
      (mul_nonneg (sq_nonneg r) (sq_nonneg z))]
  exact ⟨⟨harg1pos, harg1lt⟩, ⟨hargRpos, hargRlt⟩, horder⟩

theorem radialEulerCrossCore_neg_physical
    {rho r z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : 0 < r)
    (hz : 0 < z)
    (hupper : (1 + r) * z < 1) :
    radialEulerCrossCore rho r z < 0 := by
  obtain ⟨harg1, hargR, horder⟩ :=
    radialEulerLogArg_order_physical hrho hr hz hupper
  have hq : 1 - z ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [mul_pos hr hz]
  exact radialEulerCrossCore_neg_of_arg_order hz hq harg1 hargR horder

theorem radialEulerLog_pos_of_arg
    {c r z : ℝ} (harg : radialEulerLogArg c r z ∈ Ioo (0 : ℝ) 1) :
    0 < radialEulerLog c r z := by
  unfold radialEulerLog
  nlinarith [Real.log_neg harg.1 harg.2]

/-- The radial Euler ratio is strictly decreasing on every nondegenerate open
ray cell. This replaces the manuscript's power-series proof by the elementary
logarithmic-fraction monotonicity argument above. -/
theorem radialEulerLogRatio_strictAntiOn_physical
    {rho r : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : 0 < r) :
    StrictAntiOn (radialEulerLogRatio rho r)
      (Ioo (0 : ℝ) (1 + r)⁻¹) := by
  have h1r : 0 < 1 + r := by linarith
  let D : Set ℝ := Ioo (0 : ℝ) (1 + r)⁻¹
  have hphysical : ∀ z ∈ D,
      radialEulerLogArg 1 r z ∈ Ioo (0 : ℝ) (1 - z) ∧
        radialEulerLogArg rho r z ∈ Ioo (0 : ℝ) (1 - z) ∧
        radialEulerLogArg 1 r z < radialEulerLogArg rho r z := by
    intro z hz
    have hupper : (1 + r) * z < 1 := by
      calc
        (1 + r) * z = z * (1 + r) := mul_comm _ _
        _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
        _ = 1 := inv_mul_cancel₀ h1r.ne'
    exact radialEulerLogArg_order_physical hrho hr hz.1 hupper
  change StrictAntiOn (radialEulerLogRatio rho r) D
  apply strictAntiOn_radialEulerLogRatio_of_crossNumerator_neg
      (convex_Ioo (0 : ℝ) (1 + r)⁻¹)
  · intro z hz
    exact (hphysical z hz).2.1.1.ne'
  · intro z hz
    exact (hphysical z hz).1.1.ne'
  · intro z hz
    have hq1 : 1 - z < 1 := by linarith [hz.1]
    exact (radialEulerLog_pos_of_arg
      ⟨(hphysical z hz).1.1, (hphysical z hz).1.2.trans hq1⟩).ne'
  · intro z hz
    rw [interior_Ioo] at hz
    obtain ⟨harg1, hargR, horder⟩ := hphysical z hz
    rw [radialEulerRatioCrossNumerator_lt_zero_iff_core hargR.1 harg1.1]
    have hupper : (1 + r) * z < 1 := by
      calc
        (1 + r) * z = z * (1 + r) := mul_comm _ _
        _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
        _ = 1 := inv_mul_cancel₀ h1r.ne'
    exact radialEulerCrossCore_neg_physical hrho hr hz.1 hupper

/-- In the genuine entropy interior, the original Euler ratio inherits the
strict decrease of its closed logarithmic form. -/
theorem radialEulerRatio_strictAntiOn_physical
    {rho r : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (radialEulerRatio rho r)
      (Ioo (0 : ℝ) (1 + r)⁻¹) := by
  apply (radialEulerLogRatio_strictAntiOn_physical hrho hr.1).congr
  intro z hz
  have h1r : 0 < 1 + r := add_pos_of_pos_of_nonneg zero_lt_one hr.1.le
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
      _ = 1 := inv_mul_cancel₀ h1r.ne'
  have hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (sub_pos.2 hr.2) hz.1
    · nlinarith [mul_pos hr.1 hz.1]
  have hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨mul_pos h1r hz.1, hupper⟩
  have hrhor_nonneg : 0 ≤ rho * r := mul_nonneg hrho.1 hr.1.le
  have hrhor_lt : rho * r < 1 := by
    have hle : rho * r ≤ r := by
      nlinarith [mul_nonneg (sub_nonneg.2 hrho.2.le) hr.1.le]
    exact hle.trans_lt hr.2
  have hrhor_le_r : rho * r ≤ r := by
    nlinarith [mul_nonneg (sub_nonneg.2 hrho.2.le) hr.1.le]
  have hRminus : (1 - rho * r) * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (sub_pos.2 hrhor_lt) hz.1
    · exact (mul_le_mul_of_nonneg_right (by linarith [hrhor_nonneg, hr.1]) hz.1.le).trans_lt
        hplus.2
  have hRplus : (1 + rho * r) * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos (by linarith) hz.1
    · exact (mul_le_mul_of_nonneg_right (by linarith [hrhor_le_r]) hz.1.le).trans_lt
        hplus.2
  exact (radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus).symm

/-- A prescribed interior Euler multiplier has at most one radial contact. -/
theorem radial_stationary_contact_unique
    {rho theta r z₁ z₂ : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz₁ : z₁ ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hz₂ : z₂ ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hstat₁ : theta * radialEulerDefect 1 r z₁ -
      radialEulerDefect rho r z₁ = 0)
    (hstat₂ : theta * radialEulerDefect 1 r z₂ -
      radialEulerDefect rho r z₂ = 0) :
    z₁ = z₂ := by
  have h1r : 0 < 1 + r := add_pos_of_pos_of_nonneg zero_lt_one hr.1.le
  have hargs : ∀ z ∈ Ioo (0 : ℝ) (1 + r)⁻¹,
      (1 - r) * z ∈ Ioo (0 : ℝ) 1 ∧
        (1 + r) * z ∈ Ioo (0 : ℝ) 1 := by
    intro z hz
    have hupper : (1 + r) * z < 1 := by
      calc
        (1 + r) * z = z * (1 + r) := mul_comm _ _
        _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
        _ = 1 := inv_mul_cancel₀ h1r.ne'
    constructor
    · constructor
      · exact mul_pos (sub_pos.2 hr.2) hz.1
      · nlinarith [mul_pos hr.1 hz.1]
    · exact ⟨mul_pos h1r hz.1, hupper⟩
  have hratio₁ : radialEulerRatio rho r z₁ = theta :=
    (radial_stationary_iff_ratio (hargs z₁ hz₁).1 (hargs z₁ hz₁).2).1 hstat₁
  have hratio₂ : radialEulerRatio rho r z₂ = theta :=
    (radial_stationary_iff_ratio (hargs z₂ hz₂).1 (hargs z₂ hz₂).2).1 hstat₂
  exact (radialEulerRatio_strictAntiOn_physical hrho hr).injOn hz₁ hz₂
    (hratio₁.trans hratio₂.symm)

end CourtadeKumar
