import InformationTheory.CourtadeKumar.NaturalTriangleGradientPath

/-! First and second numerator variations along curved radial paths. -/

open Set

namespace CourtadeKumar

noncomputable def naturalTriangleRadialPathNumerator
    (rho theta : ℝ) (z : ℝ → ℝ) (s : ℝ) : ℝ :=
  naturalTriangleLagrangian rho theta (z s) (s * z s)

noncomputable def naturalTriangleRadialPathFirst
    (rho theta : ℝ) (z dz : ℝ → ℝ) (s : ℝ) : ℝ :=
  affinePathFirstVariation
    (naturalTriangleKm rho theta (z s) (s * z s))
    (naturalTriangleKu rho theta (z s) (s * z s))
    (z s) s (dz s) 1

theorem hasDerivAt_naturalTriangleRadialPathNumerator
    {rho theta : ℝ} {z dz : ℝ → ℝ} {r : ℝ}
    (hz : HasDerivAt z (dz r) r)
    (hRminus : z r - rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hRplus : z r + rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hminus : z r - r * z r ∈ Ioo (0 : ℝ) 1)
    (hplus : z r + r * z r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (naturalTriangleRadialPathNumerator rho theta z)
      (naturalTriangleRadialPathFirst rho theta z dz r) r := by
  unfold naturalTriangleRadialPathNumerator naturalTriangleRadialPathFirst
  exact hasDerivAt_naturalTriangleLagrangian_radialPath hz
    hRminus hRplus hminus hplus

/-- The derivative of the numerator's first variation is the accelerated
second-variation formula used by the stationary quotient calculation. -/
theorem hasDerivAt_naturalTriangleRadialPathFirst
    {rho theta : ℝ} {z dz : ℝ → ℝ} {ddz r : ℝ}
    (hz : HasDerivAt z (dz r) r)
    (hdz : HasDerivAt dz ddz r)
    (hRminus : z r - rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hRplus : z r + rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hminus : z r - r * z r ∈ Ioo (0 : ℝ) 1)
    (hplus : z r + r * z r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (naturalTriangleRadialPathFirst rho theta z dz)
      (acceleratedPathSecondVariation
        (naturalTriangleKm rho theta (z r) (r * z r))
        (naturalTriangleKu rho theta (z r) (r * z r))
        (naturalTriangleKmm rho theta (z r) (r * z r))
        (naturalTriangleKmu rho theta (z r) (r * z r))
        (naturalTriangleKuu rho theta (z r) (r * z r))
        (z r) r (dz r) 1 ddz 0) r := by
  have hu0 := (hasDerivAt_id r).mul hz
  have hu : HasDerivAt (fun s ↦ s * z s) (r * dz r + z r) r := by
    simpa [id_eq, add_comm] using hu0
  have hKm := hasDerivAt_naturalTriangleKm_comp
    (rho := rho) (theta := theta) hz hu
    hRminus hRplus hminus hplus
  have hKu := hasDerivAt_naturalTriangleKu_comp
    (rho := rho) (theta := theta) hz hu
    hRminus hRplus hminus hplus
  have hdu0 := ((hasDerivAt_id r).mul hdz).add hz
  have hdu : HasDerivAt (fun s ↦ s * dz s + z s)
      (r * ddz + 2 * dz r) r := by
    convert hdu0 using 1 <;> simp [id_eq] <;> ring
  have hfirst := (hKm.mul hdz).add (hKu.mul hdu)
  unfold naturalTriangleRadialPathFirst
  convert hfirst using 1
  · funext s
    unfold affinePathFirstVariation
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · unfold acceleratedPathSecondVariation affinePathSecondVariation
    ring

end CourtadeKumar
