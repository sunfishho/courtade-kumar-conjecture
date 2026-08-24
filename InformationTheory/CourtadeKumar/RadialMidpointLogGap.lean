import InformationTheory.CourtadeKumar.RadialLagrangianHessian

/-! Scalar logarithmic inequalities for the lower radial branch. -/

open Set

namespace CourtadeKumar

theorem log_one_plus_gt_div {x : ℝ} (hx : 0 < x) :
    x / (1 + x) < Real.log (1 + x) := by
  have hpos : 0 < (1 + x)⁻¹ := inv_pos.2 (by linarith)
  have hne : (1 + x)⁻¹ ≠ 1 := by
    intro h
    have := congrArg (fun y : ℝ ↦ y * (1 + x)) h
    field_simp at this
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hpos hne
  rw [Real.log_inv] at hlog
  field_simp [show 1 + x ≠ 0 by linarith] at hlog ⊢
  nlinarith

theorem complement_square_mul_log_pos
    {z : ℝ} (hz : z ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < (1 - z) ^ 2 * Real.log ((1 - z) ^ 2) -
      z ^ 2 * Real.log (z ^ 2) := by
  let a : ℝ := 1 - z
  let t : ℝ := z / a
  have ha : 0 < a := by dsimp [a]; linarith [hz.2]
  have ht : 1 < t := by
    dsimp [t]
    rw [lt_div_iff₀ ha]
    dsimp [a]
    linarith [hz.1]
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hrecip : 0 < t⁻¹ := inv_pos.2 ht0
  have hL : 1 / (t + 1) < Real.log (1 + 1 / t) := by
    have h := log_one_plus_gt_div hrecip
    convert h using 1 <;> field_simp [ht0.ne']
  have hlogt : Real.log t < t - 1 :=
    Real.log_lt_sub_one_of_pos ht0 ht.ne'
  have hfactor : 0 < t ^ 2 - 1 := by nlinarith
  have hstep : Real.log t <
      (t ^ 2 - 1) * Real.log (1 + 1 / t) := by
    have hm := mul_lt_mul_of_pos_left hL hfactor
    have hden : t + 1 ≠ 0 := by linarith
    have hcalc : (t ^ 2 - 1) * (1 / (t + 1)) = t - 1 := by
      field_simp [hden]
      ring
    rw [hcalc] at hm
    exact hlogt.trans hm
  have hG : 0 < t ^ 2 * Real.log (1 + 1 / t) - Real.log (1 + t) := by
    have hlogmul : Real.log (t * (1 + 1 / t)) =
        Real.log t + Real.log (1 + 1 / t) := by
      rw [Real.log_mul ht0.ne' (by positivity : 1 + 1 / t ≠ 0)]
    have hprod : t * (1 + 1 / t) = 1 + t := by
      field_simp [ht0.ne']
      ring
    rw [hprod] at hlogmul
    rw [hlogmul]
    linarith
  have hza : z = t * a := by
    dsimp [t]
    field_simp [ha.ne']
  have hsum : z + a = 1 := by dsimp [a]; ring
  have hza_pos : 0 < z := lt_trans (by norm_num) hz.1
  have hlogz : Real.log (1 + 1 / t) = -Real.log z := by
    have heq : 1 + 1 / t = z⁻¹ := by
      rw [hza]
      field_simp [ht0.ne', ha.ne']
      nlinarith [hsum]
    rw [heq, Real.log_inv]
  have hloga : Real.log (1 + t) = -Real.log a := by
    have heq : 1 + t = a⁻¹ := by
      dsimp [t]
      field_simp [ha.ne']
      linarith [hsum]
    rw [heq, Real.log_inv]
  rw [hlogz, hloga] at hG
  have hamul := mul_pos (sq_pos_of_pos ha) hG
  rw [mul_sub] at hamul
  have ht_sq : a ^ 2 * t ^ 2 = z ^ 2 := by rw [hza]; ring
  have hlogsq_a : Real.log (a ^ 2) = 2 * Real.log a := by
    rw [Real.log_pow]
    norm_num
  have hlogsq_z : Real.log (z ^ 2) = 2 * Real.log z := by
    rw [Real.log_pow]
    norm_num
  have hscaled : 0 < -(a ^ 2 * t ^ 2) * Real.log z +
      a ^ 2 * Real.log a := by
    nlinarith [hamul]
  rw [ht_sq] at hscaled
  dsimp [a] at hscaled ⊢
  rw [hlogsq_a, hlogsq_z]
  nlinarith [hscaled]

theorem shifted_mul_log_gap_strictAntiOn {d : ℝ} (hd : 0 < d) :
    StrictAntiOn (fun x : ℝ ↦
      x * Real.log x - (x + d) * Real.log (x + d)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (Real.continuous_mul_log.comp continuous_id).continuousWithinAt.sub
      (Real.continuous_mul_log.comp
        (continuous_id.add continuous_const)).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hxd : 0 < x + d := by linarith
    have hleft := Real.hasDerivAt_mul_log hx.ne'
    have hright := (Real.hasDerivAt_mul_log hxd.ne').comp x
      ((hasDerivAt_id x).add_const d)
    have hder : HasDerivAt
        (fun x : ℝ ↦ x * Real.log x - (x + d) * Real.log (x + d))
        ((Real.log x + 1) - (Real.log (x + d) + 1)) x := by
      simpa only [Function.comp_apply, id_eq, mul_one] using hleft.sub hright
    rw [hder.deriv]
    have hlog : Real.log x < Real.log (x + d) :=
      Real.strictMonoOn_log hx hxd (by linarith)
    linarith

theorem shifted_mul_log_gap_pos
    {a d x : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hx : x ∈ Ioo (0 : ℝ) a)
    (hbase : 0 < a * Real.log a - (a + d) * Real.log (a + d)) :
    0 < x * Real.log x - (x + d) * Real.log (x + d) := by
  have hanti := shifted_mul_log_gap_strictAntiOn hd hx.1 ha hx.2
  exact hbase.trans hanti

noncomputable def radialEulerMassArg (c r z : ℝ) : ℝ :=
  z ^ 2 - c ^ 2 * r ^ 2 * z ^ 2

theorem radialEulerMassArg_eq_logArg_add (c r z : ℝ) :
    radialEulerMassArg c r z = radialEulerLogArg c r z + (2 * z - 1) := by
  unfold radialEulerMassArg radialEulerLogArg
  ring

theorem radialEuler_mul_log_gap_pos
    {c r z : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hz : z ∈ Ioo (1 / 2 : ℝ) 1)
    (harg : 0 < radialEulerLogArg c r z) :
    0 < radialEulerLogArg c r z * Real.log (radialEulerLogArg c r z) -
      radialEulerMassArg c r z * Real.log (radialEulerMassArg c r z) := by
  let a : ℝ := (1 - z) ^ 2
  let d : ℝ := 2 * z - 1
  let x : ℝ := radialEulerLogArg c r z
  have ha : 0 < a := sq_pos_of_pos (by linarith [hz.2])
  have hd : 0 < d := by dsimp [d]; linarith [hz.1]
  have hxlt : x < a := by
    dsimp [x, a]
    unfold radialEulerLogArg
    have hspread : 0 < c ^ 2 * r ^ 2 * z ^ 2 :=
      mul_pos (mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hr))
        (sq_pos_of_pos (lt_trans (by norm_num) hz.1))
    nlinarith
  have hbase : 0 < a * Real.log a - (a + d) * Real.log (a + d) := by
    have hcomp := complement_square_mul_log_pos hz
    have had : a + d = z ^ 2 := by dsimp [a, d]; ring
    simpa [a, had] using hcomp
  have hgap := shifted_mul_log_gap_pos ha hd ⟨harg, hxlt⟩ hbase
  rw [radialEulerMassArg_eq_logArg_add]
  simpa [x, d] using hgap

end CourtadeKumar
