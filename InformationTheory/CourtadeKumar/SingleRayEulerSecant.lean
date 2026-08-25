import InformationTheory.CourtadeKumar.SingleRayGainRatioReduction
import InformationTheory.CourtadeKumar.RadialEulerCrossSign
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Cauchy-mean-value representation of radial entropy-ratio losses. -/

open Set

namespace CourtadeKumar

noncomputable def radialNatEntropyRatio (c r z : ℝ) : ℝ :=
  radialNatEntropy c r z / z

theorem radialNatEntropyRatio_one_eq_bits (r z : ℝ) :
    radialNatEntropyRatio 1 r z = Real.log 2 * radialEntropyRatio r z := by
  unfold radialNatEntropyRatio radialEntropyRatio
  rw [radialTriangleEntropy_eq_nat]
  field_simp [log_two_ne_zero]

theorem hasDerivAt_radialNatEntropyRatio
    {c r z : ℝ} (hz : z ≠ 0)
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatEntropyRatio c r)
      (-radialEulerDefect c r z / z ^ 2) z := by
  have hentropy := hasDerivAt_radialNatEntropy hminus hplus
  have hquot := hentropy.div (hasDerivAt_id z) hz
  unfold radialNatEntropyRatio radialEulerDefect
  convert hquot using 1 <;> simp only [id_eq] <;>
    field_simp [hz] <;> ring

/-- Between two physical masses, the two radial entropy-ratio losses have
the Euler ratio at an intermediate mass as their exact secant slope. -/
theorem exists_radialEulerRatio_secant
    {rho r M z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    ∃ ξ ∈ Ioo M z,
      (radialNatEntropyRatio 1 r M - radialNatEntropyRatio 1 r z) *
          radialEulerDefect rho r ξ =
        (radialNatEntropyRatio rho r M -
            radialNatEntropyRatio rho r z) *
          radialEulerDefect 1 r ξ := by
  have hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := ⟨hM.trans hMz, hzupper⟩
  have hargs : ∀ x ∈ Icc M z,
      (1 - rho * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + rho * r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 - r) * x ∈ Ioo (0 : ℝ) 1 ∧
        (1 + r) * x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact radialEntropyArgs_physical hrho hr
      ⟨hM.trans_le hx.1, hx.2.trans_lt hzupper⟩
  let f : ℝ → ℝ := radialNatEntropyRatio rho r
  let g : ℝ → ℝ := radialNatEntropyRatio 1 r
  let f' : ℝ → ℝ := fun x ↦ -radialEulerDefect rho r x / x ^ 2
  let g' : ℝ → ℝ := fun x ↦ -radialEulerDefect 1 r x / x ^ 2
  have hfderiv : ∀ x ∈ Ioo M z, HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : x ∈ Icc M z := ⟨hx.1.le, hx.2.le⟩
    exact hasDerivAt_radialNatEntropyRatio (ne_of_gt (hM.trans hx.1))
      (hargs x hx').1 (hargs x hx').2.1
  have hgderiv : ∀ x ∈ Ioo M z, HasDerivAt g (g' x) x := by
    intro x hx
    have hx' : x ∈ Icc M z := ⟨hx.1.le, hx.2.le⟩
    exact hasDerivAt_radialNatEntropyRatio (ne_of_gt (hM.trans hx.1))
      (by simpa using (hargs x hx').2.2.1)
      (by simpa using (hargs x hx').2.2.2)
  have hfcont : ContinuousOn f (Icc M z) := by
    intro x hx
    exact (hasDerivAt_radialNatEntropyRatio
      (ne_of_gt (hM.trans_le hx.1))
      (hargs x hx).1 (hargs x hx).2.1).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Icc M z) := by
    intro x hx
    exact (hasDerivAt_radialNatEntropyRatio
      (ne_of_gt (hM.trans_le hx.1))
      (by simpa using (hargs x hx).2.2.1)
      (by simpa using (hargs x hx).2.2.2)).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hsecant⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    f f' hMz hfcont hfderiv g g' hgcont hgderiv
  refine ⟨ξ, hξ, ?_⟩
  dsimp [f, g, f', g'] at hsecant ⊢
  have hξ0 : ξ ≠ 0 := ne_of_gt (hM.trans hξ.1)
  field_simp [hξ0] at hsecant
  linarith

/-- Ratio form of the same secant identity.  The denominator is strictly
positive because input entropy per unit mass strictly decreases outward. -/
theorem exists_radialEulerRatio_eq_ratioLoss
    {rho r M z : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < M) (hMz : M < z)
    (hzupper : z < (1 + r)⁻¹) :
    ∃ ξ ∈ Ioo M z,
      (radialNatEntropyRatio rho r M -
          radialNatEntropyRatio rho r z) /
          (radialNatEntropyRatio 1 r M -
            radialNatEntropyRatio 1 r z) =
        radialEulerRatio rho r ξ := by
  obtain ⟨ξ, hξ, hsecant⟩ := exists_radialEulerRatio_secant
    hrho hr hM hMz hzupper
  have hMdom : M ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM, hMz.trans hzupper⟩
  have hzdom : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.trans hMz, hzupper⟩
  have hbits := strictAntiOn_radialEntropyRatio hr hMdom hzdom hMz
  have hinput : 0 < radialNatEntropyRatio 1 r M -
      radialNatEntropyRatio 1 r z := by
    rw [radialNatEntropyRatio_one_eq_bits,
      radialNatEntropyRatio_one_eq_bits]
    simpa [mul_sub] using
      mul_pos (Real.log_pos one_lt_two) (sub_pos.mpr hbits)
  have hξdom : ξ ∈ Ioo (0 : ℝ) (1 + r)⁻¹ :=
    ⟨hM.trans hξ.1, hξ.2.trans hzupper⟩
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hr hξdom
  have hEuler1 : radialEulerDefect 1 r ξ ≠ 0 :=
    (radialEulerDefect_pos (by simpa using hminus)
      (by simpa using hplus)).ne'
  refine ⟨ξ, hξ, ?_⟩
  unfold radialEulerRatio
  rw [div_eq_div_iff hinput.ne' hEuler1]
  simpa [mul_comm] using hsecant.symm

end CourtadeKumar
