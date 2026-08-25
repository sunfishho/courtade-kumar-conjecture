import InformationTheory.CourtadeKumar.RadialPerspective

/-! Differential identity for the radial perspective quotient. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Natural-log entropy profile with radial contraction factor `c`. -/
noncomputable def radialNatEntropy (c r z : ℝ) : ℝ :=
  (Real.binEntropy ((1 - c * r) * z) +
    Real.binEntropy ((1 + c * r) * z)) / 2

noncomputable def radialNatEntropyDeriv (c r z : ℝ) : ℝ :=
  ((1 - c * r) *
      (Real.log (1 - (1 - c * r) * z) - Real.log ((1 - c * r) * z)) +
    (1 + c * r) *
      (Real.log (1 - (1 + c * r) * z) - Real.log ((1 + c * r) * z))) / 2

/-- The Euler defect `f - z f'` of a radial natural-entropy profile. -/
noncomputable def radialEulerDefect (c r z : ℝ) : ℝ :=
  radialNatEntropy c r z - z * radialNatEntropyDeriv c r z

theorem hasDerivAt_radialNatEntropy
    {c r z : ℝ}
    (hminus : (1 - c * r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + c * r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatEntropy c r)
      (radialNatEntropyDeriv c r z) z := by
  have hargMinus : HasDerivAt (fun w : ℝ ↦ (1 - c * r) * w) (1 - c * r) z := by
    simpa [id_eq] using (hasDerivAt_id z).const_mul (1 - c * r)
  have hargPlus : HasDerivAt (fun w : ℝ ↦ (1 + c * r) * w) (1 + c * r) z := by
    simpa [id_eq] using (hasDerivAt_id z).const_mul (1 + c * r)
  have hm := (Real.hasDerivAt_binEntropy hminus.1.ne' hminus.2.ne).comp z hargMinus
  have hp := (Real.hasDerivAt_binEntropy hplus.1.ne' hplus.2.ne).comp z hargPlus
  unfold radialNatEntropy radialNatEntropyDeriv
  convert (hm.add hp).div_const 2 using 1 <;>
    simp [Function.comp_apply, Real.deriv_binEntropy] <;> ring

noncomputable def radialNatDifference
    (alpha : ℝ≥0) (theta r z : ℝ) : ℝ :=
  radialNatEntropy (channelRho (alpha : ℝ)) r z -
    theta * radialNatEntropy 1 r z

theorem radialTriangleDifference_eq_nat
    (alpha : ℝ≥0) (theta r z : ℝ) :
    radialTriangleDifference alpha theta r z =
      radialNatDifference alpha theta r z / Real.log 2 := by
  unfold radialTriangleDifference radialTriangleChannelEntropy
    radialTriangleEntropy radialNatDifference radialNatEntropy binaryEntropyBits
  ring

/-- Natural-unit derivative of the single-ray Lagrangian. -/
theorem hasDerivAt_radialNatDifference
    {alpha : ℝ≥0} {theta r z : ℝ}
    (hRminus : (1 - channelRho (alpha : ℝ) * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + channelRho (alpha : ℝ) * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialNatDifference alpha theta r)
      (radialNatEntropyDeriv (channelRho (alpha : ℝ)) r z -
        theta * radialNatEntropyDeriv 1 r z) z := by
  unfold radialNatDifference
  have hone := hasDerivAt_radialNatEntropy (c := (1 : ℝ)) (r := r) (z := z)
    (by simpa using hminus) (by simpa using hplus)
  exact (hasDerivAt_radialNatEntropy hRminus hRplus).sub
    (hone.const_mul theta)

/-- Exact Euler-defect formula for the derivative of the natural-unit
perspective quotient. -/
theorem hasDerivAt_radialNatDifference_div
    {alpha : ℝ≥0} {theta r z : ℝ}
    (hz : z ≠ 0)
    (hRminus : (1 - channelRho (alpha : ℝ) * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + channelRho (alpha : ℝ) * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w ↦ radialNatDifference alpha theta r w / w)
      ((theta * radialEulerDefect 1 r z -
        radialEulerDefect (channelRho (alpha : ℝ)) r z) / z ^ 2) z := by
  have hdiff := hasDerivAt_radialNatDifference (theta := theta)
    hRminus hRplus hminus hplus
  have hquot := hdiff.div (hasDerivAt_id z) hz
  convert hquot using 1 <;>
    simp only [id_eq] <;>
    unfold radialEulerDefect radialNatDifference <;>
    field_simp [hz] <;> ring

/-- Bit-valued form of the same derivative identity. -/
theorem hasDerivAt_radialTriangleDifference_div
    {alpha : ℝ≥0} {theta r z : ℝ}
    (hz : z ≠ 0)
    (hRminus : (1 - channelRho (alpha : ℝ) * r) * z ∈ Ioo (0 : ℝ) 1)
    (hRplus : (1 + channelRho (alpha : ℝ) * r) * z ∈ Ioo (0 : ℝ) 1)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w ↦ radialTriangleDifference alpha theta r w / w)
      ((theta * radialEulerDefect 1 r z -
          radialEulerDefect (channelRho (alpha : ℝ)) r z) /
        (Real.log 2 * z ^ 2)) z := by
  have hnat := hasDerivAt_radialNatDifference_div (theta := theta)
    hz hRminus hRplus hminus hplus
  have hscaled := hnat.div_const (Real.log 2)
  convert hscaled using 1
  · funext w
    rw [radialTriangleDifference_eq_nat]
    ring
  · field_simp [log_two_ne_zero, hz]

end CourtadeKumar
