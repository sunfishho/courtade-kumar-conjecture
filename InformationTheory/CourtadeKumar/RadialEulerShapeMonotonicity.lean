import InformationTheory.CourtadeKumar.RadialOneRay

/-! Monotonicity of the Euler ratio in the ray-shape variable. -/

open Set

namespace CourtadeKumar

noncomputable def radialEulerLogShapeDeriv (c r z : ℝ) : ℝ :=
  c ^ 2 * r * z ^ 2 / radialEulerLogArg c r z

noncomputable def radialEulerShapeCrossNumerator (rho r z : ℝ) : ℝ :=
  radialEulerLogShapeDeriv rho r z * radialEulerLog 1 r z -
    radialEulerLog rho r z * radialEulerLogShapeDeriv 1 r z

noncomputable def radialEulerShapeCrossCore (rho r z : ℝ) : ℝ :=
  radialEulerLogArg rho r z * Real.log (radialEulerLogArg rho r z) -
    rho ^ 2 * radialEulerLogArg 1 r z *
      Real.log (radialEulerLogArg 1 r z)

theorem hasDerivAt_radialEulerLog_shape
    {c r z : ℝ} (harg : radialEulerLogArg c r z ≠ 0) :
    HasDerivAt (fun s ↦ radialEulerLog c s z)
      (radialEulerLogShapeDeriv c r z) r := by
  have hinner : HasDerivAt (fun s ↦ radialEulerLogArg c s z)
      (-2 * c ^ 2 * r * z ^ 2) r := by
    unfold radialEulerLogArg
    convert (hasDerivAt_const r ((1 - z) ^ 2)).sub
      (((hasDerivAt_id r).pow 2).const_mul (c ^ 2 * z ^ 2)) using 1
    · funext s
      simp [id_eq]
      ring
    · simp [id_eq]
      ring
  have hlog := (Real.hasDerivAt_log harg).comp r hinner
  unfold radialEulerLog radialEulerLogShapeDeriv
  convert hlog.const_mul (-(1 / 2 : ℝ)) using 1
  field_simp [harg]

theorem hasDerivAt_radialEulerLogRatio_shape
    {rho r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0)
    (hden : radialEulerLog 1 r z ≠ 0) :
    HasDerivAt (fun s ↦ radialEulerLogRatio rho s z)
      (radialEulerShapeCrossNumerator rho r z /
        radialEulerLog 1 r z ^ 2) r := by
  have hR := hasDerivAt_radialEulerLog_shape hargR
  have h1 := hasDerivAt_radialEulerLog_shape harg1
  unfold radialEulerLogRatio radialEulerShapeCrossNumerator
  exact hR.div h1 hden

theorem radialEulerShapeCrossNumerator_eq_core
    {rho r z : ℝ}
    (hargR : radialEulerLogArg rho r z ≠ 0)
    (harg1 : radialEulerLogArg 1 r z ≠ 0) :
    radialEulerShapeCrossNumerator rho r z =
      r * z ^ 2 * radialEulerShapeCrossCore rho r z /
        (2 * radialEulerLogArg rho r z * radialEulerLogArg 1 r z) := by
  unfold radialEulerShapeCrossNumerator radialEulerLogShapeDeriv
    radialEulerLog radialEulerShapeCrossCore
  field_simp [hargR, harg1]
  ring

theorem radialEulerShapeCrossCore_neg_physical
    {rho r z : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (hz : 0 < z)
    (hupper : (1 + r) * z < 1) :
    radialEulerShapeCrossCore rho r z < 0 := by
  let Q : ℝ := (1 - z) ^ 2
  let x : ℝ := radialEulerLogArg 1 r z
  let y : ℝ := radialEulerLogArg rho r z
  have hz1 : z < 1 := by nlinarith [mul_pos hr hz]
  have hQ : Q ∈ Ioo (0 : ℝ) 1 := by
    dsimp [Q]
    constructor
    · exact sq_pos_of_pos (sub_pos.2 hz1)
    · nlinarith [mul_pos hz (sub_pos.2 hz1)]
  have hargs := radialEulerLogArg_order_physical
    (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩) hr hz hupper
  have hxpos : 0 < x := hargs.1.1
  have hypos : 0 < y := hargs.2.1.1
  have hxQ : x < Q := by
    dsimp [x, Q]
    unfold radialEulerLogArg
    nlinarith [mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hz)]
  have hyQ : y < Q := by
    dsimp [y, Q]
    unfold radialEulerLogArg
    have hspread : 0 < rho ^ 2 * r ^ 2 * z ^ 2 :=
      mul_pos (mul_pos (sq_pos_of_pos hrho.1) (sq_pos_of_pos hr))
        (sq_pos_of_pos hz)
    nlinarith
  have hxy : x < y := hargs.2.2
  have hcross := log_cross_neg_of_lt hQ ⟨hxpos, hxQ⟩ ⟨hypos, hyQ⟩ hxy
  have heq : y * (Q - x) * Real.log y -
      x * (Q - y) * Real.log x =
      r ^ 2 * z ^ 2 * radialEulerShapeCrossCore rho r z := by
    dsimp [x, y, Q]
    unfold radialEulerShapeCrossCore
    simp only [radialEulerLogArg]
    ring
  rw [heq] at hcross
  have hfactor : 0 < r ^ 2 * z ^ 2 :=
    mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hz)
  by_contra hn
  exact (not_lt_of_ge (mul_nonneg hfactor.le (le_of_not_gt hn))) hcross

theorem deriv_radialEulerLogRatio_shape_neg_physical
    {rho r z : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (hz : 0 < z)
    (hupper : (1 + r) * z < 1) :
    deriv (fun s ↦ radialEulerLogRatio rho s z) r < 0 := by
  obtain ⟨harg1, hargR, _⟩ := radialEulerLogArg_order_physical
    (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩) hr hz hupper
  have hz1 : z < 1 := by nlinarith [mul_pos hr hz]
  have hden : radialEulerLog 1 r z ≠ 0 :=
    (radialEulerLog_pos_of_arg ⟨harg1.1, harg1.2.trans (by linarith)⟩).ne'
  rw [(hasDerivAt_radialEulerLogRatio_shape hargR.1.ne' harg1.1.ne' hden).deriv]
  apply div_neg_of_neg_of_pos
  · rw [radialEulerShapeCrossNumerator_eq_core hargR.1.ne' harg1.1.ne']
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos hr (sq_pos_of_pos hz))
        (radialEulerShapeCrossCore_neg_physical hrho hr hz hupper))
      (mul_pos (mul_pos (by norm_num) hargR.1) harg1.1)
  · exact sq_pos_of_ne_zero hden

/-- At the centered radial location, the Euler multiplier strictly decreases
with the ray shape. -/
theorem centeredRadialMultiplier_strictAntiOn
    {rho : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun r ↦ radialEulerLogRatio rho r (1 / 2))
      (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro r hr
    have hupper : (1 + r) * (1 / 2 : ℝ) < 1 := by nlinarith [hr.2]
    obtain ⟨harg1, hargR, _⟩ := radialEulerLogArg_order_physical
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
      hr.1 (by norm_num) hupper
    have hden : radialEulerLog 1 r (1 / 2) ≠ 0 :=
      (radialEulerLog_pos_of_arg
        ⟨harg1.1, harg1.2.trans (by norm_num)⟩).ne'
    exact (hasDerivAt_radialEulerLogRatio_shape
      hargR.1.ne' harg1.1.ne' hden).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact deriv_radialEulerLogRatio_shape_neg_physical
      hrho hr.1 (by norm_num) (by nlinarith [hr.2])

end CourtadeKumar
