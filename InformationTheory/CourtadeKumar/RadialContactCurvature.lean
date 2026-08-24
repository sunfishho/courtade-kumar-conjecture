import InformationTheory.CourtadeKumar.EntropyHessian

/-! Strict directional curvature at lower-half radial contacts. -/

open Set

namespace CourtadeKumar

theorem radialEulerDefect_eq_loewnerSigmaDelta
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    radialEulerDefect c r z =
      loewnerSigmaDelta z (r * z) (c ^ 2) := by
  rw [radialEulerDefect_eq_log hminus hplus]
  unfold loewnerSigmaDelta loewnerSigmaEll
  rw [show loewnerSigmaY z (r * z) (c ^ 2) =
      (1 - z) ^ 2 - c ^ 2 * r ^ 2 * z ^ 2 by
    unfold loewnerSigmaY
    ring]
  ring

noncomputable def radialLagrangianDirectionalCurvature
    (rho theta z r x y : ℝ) : ℝ :=
  theta * scaledNatEntropyNegCurvature 1 z (r * z) x y -
    scaledNatEntropyNegCurvature rho z (r * z) x y

/-- At every stationary contact strictly below the centered line, the
natural-unit Lagrangian has positive curvature in every nonzero direction. -/
theorem radialLagrangianDirectionalCurvature_pos
    {rho theta z r x y : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹)
    (hzhalf : z < 1 / 2)
    (hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < radialLagrangianDirectionalCurvature rho theta z r x y := by
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1.le, hrho.2.le⟩
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrhoIcc hr hz
  have hscaledRminus : z - rho * (r * z) ∈ Ioo (0 : ℝ) 1 := by
    convert hRminus using 1 <;> ring
  have hscaledRplus : z + rho * (r * z) ∈ Ioo (0 : ℝ) 1 := by
    convert hRplus using 1 <;> ring
  have hscaled1minus : z - 1 * (r * z) ∈ Ioo (0 : ℝ) 1 := by
    convert hminus using 1 <;> ring
  have hscaled1plus : z + 1 * (r * z) ∈ Ioo (0 : ℝ) 1 := by
    convert hplus using 1 <;> ring
  have hD1 : 0 < radialEulerDefect 1 r z :=
    radialEulerDefect_pos (by simpa using hminus) (by simpa using hplus)
  have hDR : 0 < radialEulerDefect rho r z :=
    radialEulerDefect_pos (by simpa using hRminus) (by simpa using hRplus)
  have hD1eq := radialEulerDefect_eq_loewnerSigmaDelta
    (c := (1 : ℝ)) (r := r) (z := z)
    (by simpa using hminus) (by simpa using hplus)
  have hDReq := radialEulerDefect_eq_loewnerSigmaDelta
    (c := rho) (r := r) (z := z) hRminus hRplus
  have hDelta1 : loewnerSigmaDelta z (r * z) (1 ^ 2) ≠ 0 := by
    rw [← hD1eq]
    exact hD1.ne'
  have hDeltaR : loewnerSigmaDelta z (r * z) (rho ^ 2) ≠ 0 := by
    rw [← hDReq]
    exact hDR.ne'
  have hphysical : ∀ sigma ∈ Icc (rho ^ 2) 1,
      sigma * (r * z) ^ 2 / z ^ 2 ∈ Ico (0 : ℝ) 1 := by
    intro sigma hsigma
    have heq : sigma * (r * z) ^ 2 / z ^ 2 = sigma * r ^ 2 := by
      field_simp [hz.1.ne']
    rw [heq]
    constructor
    · exact mul_nonneg (le_trans (sq_nonneg rho) hsigma.1) (sq_nonneg r)
    · have hr2 : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
      exact (mul_le_mul_of_nonneg_right hsigma.2 (sq_nonneg r)).trans_lt
        (by simpa using hr2)
  have hnormalized :
      loewnerNormalizedQuadratic z (r * z) x y (rho ^ 2) <
        loewnerNormalizedQuadratic z (r * z) x y 1 := by
    apply loewnerNormalizedQuadratic_lt
      (p := z) (u := r * z) (x := x) (y := y)
      ⟨hz.1, hzhalf⟩ (mul_ne_zero hr.1.ne' hz.1.ne') hxy
    · have hprod : 0 < (1 - rho) * (1 + rho) :=
        mul_pos (sub_pos.2 hrho.2) (by linarith [hrho.1])
      nlinarith
    · exact hphysical
  have hcurv1 : scaledNatEntropyNegCurvature 1 z (r * z) x y =
      loewnerGQuadratic z (r * z) x y (1 ^ 2) :=
    scaledNatEntropyNegCurvature_eq_loewner
      (c := (1 : ℝ)) (p := z) (u := r * z) (x := x) (y := y)
    hscaled1minus.1.ne' hscaled1minus.2.ne
    hscaled1plus.1.ne' hscaled1plus.2.ne
  have hcurvR : scaledNatEntropyNegCurvature rho z (r * z) x y =
      loewnerGQuadratic z (r * z) x y (rho ^ 2) :=
    scaledNatEntropyNegCurvature_eq_loewner
      (c := rho) (p := z) (u := r * z) (x := x) (y := y)
      hscaledRminus.1.ne' hscaledRminus.2.ne
      hscaledRplus.1.ne' hscaledRplus.2.ne
  have hG1 : loewnerGQuadratic z (r * z) x y (1 ^ 2) =
      loewnerSigmaDelta z (r * z) (1 ^ 2) *
        loewnerNormalizedQuadratic z (r * z) x y (1 ^ 2) :=
    loewnerGQuadratic_eq_normalized hDelta1
  have hGR : loewnerGQuadratic z (r * z) x y (rho ^ 2) =
      loewnerSigmaDelta z (r * z) (rho ^ 2) *
        loewnerNormalizedQuadratic z (r * z) x y (rho ^ 2) :=
    loewnerGQuadratic_eq_normalized hDeltaR
  unfold radialLagrangianDirectionalCurvature
  rw [hcurv1, hcurvR, hG1, hGR, ← hD1eq, ← hDReq]
  simp only [one_pow]
  have hgap : 0 <
      loewnerNormalizedQuadratic z (r * z) x y 1 -
        loewnerNormalizedQuadratic z (r * z) x y (rho ^ 2) :=
    sub_pos.2 hnormalized
  have hstationary : theta * radialEulerDefect 1 r z =
      radialEulerDefect rho r z := by linarith
  calc
    theta * (radialEulerDefect 1 r z *
          loewnerNormalizedQuadratic z (r * z) x y 1) -
        radialEulerDefect rho r z *
          loewnerNormalizedQuadratic z (r * z) x y (rho ^ 2) =
        (theta * radialEulerDefect 1 r z) *
          loewnerNormalizedQuadratic z (r * z) x y 1 -
        radialEulerDefect rho r z *
          loewnerNormalizedQuadratic z (r * z) x y (rho ^ 2) := by ring
    _ = radialEulerDefect rho r z *
        (loewnerNormalizedQuadratic z (r * z) x y 1 -
          loewnerNormalizedQuadratic z (r * z) x y (rho ^ 2)) := by
      rw [hstationary]
      ring
    _ > 0 := mul_pos hDR hgap

end CourtadeKumar
