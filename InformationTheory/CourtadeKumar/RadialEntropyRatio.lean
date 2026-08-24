import InformationTheory.CourtadeKumar.CenteredEntropyRatio
import InformationTheory.CourtadeKumar.RadialEulerClosedForm
import InformationTheory.CourtadeKumar.RadialPerspectiveUnimodal

/-! Entropy per unit mass along a fixed radial ray. -/

open Filter Set
open scoped NNReal Topology

namespace CourtadeKumar

/-- Entropy per unit mass at radial shape `r` and mass coordinate `z`. -/
noncomputable def radialEntropyRatio (r z : ℝ) : ℝ :=
  radialTriangleEntropy r z / z

lemma radialTriangleEntropy_eq_nat (r z : ℝ) :
    radialTriangleEntropy r z = radialNatEntropy 1 r z / Real.log 2 := by
  unfold radialTriangleEntropy radialNatEntropy binaryEntropyBits
  ring

/-- The derivative of entropy per unit mass is the negative Euler defect. -/
theorem hasDerivAt_radialEntropyRatio
    {r z : ℝ} (hz : z ≠ 0)
    (hminus : (1 - r) * z ∈ Ioo (0 : ℝ) 1)
    (hplus : (1 + r) * z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialEntropyRatio r)
      (-radialEulerDefect 1 r z / (Real.log 2 * z ^ 2)) z := by
  have hnat := hasDerivAt_radialNatEntropy
    (c := (1 : ℝ)) (r := r) (z := z)
    (by simpa using hminus) (by simpa using hplus)
  have hquot := hnat.div (hasDerivAt_id z) hz
  have hscaled := hquot.div_const (Real.log 2)
  convert hscaled using 1
  · funext w
    rw [radialEntropyRatio, radialTriangleEntropy_eq_nat]
    change radialNatEntropy 1 r w / Real.log 2 / w =
      (radialNatEntropy 1 r w / w) / Real.log 2
    ring
  · unfold radialEulerDefect
    simp only [id_eq, mul_one]
    change -(radialNatEntropy 1 r z - z * radialNatEntropyDeriv 1 r z) /
        (Real.log 2 * z ^ 2) =
      (radialNatEntropyDeriv 1 r z * z - radialNatEntropy 1 r z) /
        z ^ 2 / Real.log 2
    field_simp [hz, log_two_ne_zero]
    ring

theorem deriv_radialEntropyRatio_neg
    {r z : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹) :
    deriv (radialEntropyRatio r) z < 0 := by
  obtain ⟨_, _, hminus, hplus⟩ :=
    radialEntropyArgs_physical (show (1 : ℝ) ∈ Icc 0 1 by simp) hr hz
  rw [(hasDerivAt_radialEntropyRatio hz.1.ne' hminus hplus).deriv]
  have hdefect : 0 < radialEulerDefect 1 r z :=
    radialEulerDefect_pos (by simpa using hminus) (by simpa using hplus)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hdefect)
    (mul_pos (Real.log_pos (by norm_num)) (sq_pos_of_pos hz.1))

/-- Entropy per unit mass strictly decreases throughout every physical
interior ray. -/
theorem strictAntiOn_radialEntropyRatio
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (radialEntropyRatio r)
      (Ioo (0 : ℝ) (1 + r)⁻¹) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) (1 + r)⁻¹)
  · intro z hz
    obtain ⟨_, _, hminus, hplus⟩ :=
      radialEntropyArgs_physical (show (1 : ℝ) ∈ Icc 0 1 by simp) hr hz
    exact (hasDerivAt_radialEntropyRatio hz.1.ne' hminus hplus).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    exact deriv_radialEntropyRatio_neg hr hz

lemma radialEntropyRatio_half {r : ℝ} (hr : r ≠ 0) :
    radialEntropyRatio r (1 / 2) = 2 * r * centeredEntropyRatio r := by
  rw [radialEntropyRatio, centeredEntropyRatio_eq_radial]
  field_simp [hr]

end CourtadeKumar
