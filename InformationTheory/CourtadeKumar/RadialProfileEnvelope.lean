import InformationTheory.CourtadeKumar.PerspectivePathCalculus

/-! Envelope calculus for differentiable stationary radial contacts. -/

open Set

namespace CourtadeKumar

theorem hasDerivAt_scaledNatEntropy_comp
    {c : ℝ} {p u : ℝ → ℝ} {dp du t : ℝ}
    (hp : HasDerivAt p dp t)
    (hu : HasDerivAt u du t)
    (hminus : p t - c * u t ∈ Ioo (0 : ℝ) 1)
    (hplus : p t + c * u t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ scaledNatEntropy c (p s) (u s))
      (scaledNatEntropyDirectionalFirst c (p t) (u t) dp du 0) t := by
  have hargMinus : HasDerivAt (fun s ↦ p s - c * u s) (dp - c * du) t := by
    simpa using hp.sub (hu.const_mul c)
  have hargPlus : HasDerivAt (fun s ↦ p s + c * u s) (dp + c * du) t := by
    simpa using hp.add (hu.const_mul c)
  have hm := (Real.hasDerivAt_binEntropy hminus.1.ne' hminus.2.ne).comp t hargMinus
  have hq := (Real.hasDerivAt_binEntropy hplus.1.ne' hplus.2.ne).comp t hargPlus
  unfold scaledNatEntropy scaledNatEntropyDirectionalFirst natEntropySlope
  convert (hm.add hq).div_const 2 using 1 <;> simp <;> ring

theorem hasDerivAt_naturalTriangleLagrangian_comp
    {rho theta : ℝ} {p u : ℝ → ℝ} {dp du t : ℝ}
    (hp : HasDerivAt p dp t)
    (hu : HasDerivAt u du t)
    (hRminus : p t - rho * u t ∈ Ioo (0 : ℝ) 1)
    (hRplus : p t + rho * u t ∈ Ioo (0 : ℝ) 1)
    (hminus : p t - u t ∈ Ioo (0 : ℝ) 1)
    (hplus : p t + u t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ naturalTriangleLagrangian rho theta (p s) (u s))
      (naturalTriangleDirectionalFirst rho theta (p t) (u t) dp du 0) t := by
  have hR := hasDerivAt_scaledNatEntropy_comp hp hu hRminus hRplus
  have h1 := hasDerivAt_scaledNatEntropy_comp (c := (1 : ℝ)) hp hu
    (by simpa using hminus) (by simpa using hplus)
  unfold naturalTriangleLagrangian naturalTriangleDirectionalFirst
  convert hR.sub (h1.const_mul theta) using 1

/-- First derivative of the numerator `k(z(r),r*z(r))` along an arbitrary
differentiable contact branch. -/
theorem hasDerivAt_naturalTriangleLagrangian_radialPath
    {rho theta : ℝ} {z : ℝ → ℝ} {dz r : ℝ}
    (hz : HasDerivAt z dz r)
    (hRminus : z r - rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hRplus : z r + rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hminus : z r - r * z r ∈ Ioo (0 : ℝ) 1)
    (hplus : z r + r * z r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s ↦ naturalTriangleLagrangian rho theta (z s) (s * z s))
      (affinePathFirstVariation
        (naturalTriangleKm rho theta (z r) (r * z r))
        (naturalTriangleKu rho theta (z r) (r * z r))
        (z r) r dz 1) r := by
  have hu0 := (hasDerivAt_id r).mul hz
  have hu : HasDerivAt (fun s ↦ s * z s) (r * dz + z r) r := by
    simpa [id_eq, add_comm] using hu0
  have hk := hasDerivAt_naturalTriangleLagrangian_comp
    (rho := rho) (theta := theta) hz hu
    hRminus hRplus hminus hplus
  convert hk using 1
  rw [naturalTriangleDirectionalFirst_eq_gradient]
  unfold affinePathFirstVariation
  ring

theorem stationaryQuotientFirstVariation_eq_ku
    {k km ku z r dz : ℝ}
    (hz : z ≠ 0)
    (hstationary : k = z * (km + r * ku)) :
    quotientFirstVariation k
        (affinePathFirstVariation km ku z r dz 1) z dz = ku := by
  unfold quotientFirstVariation affinePathFirstVariation
  rw [hstationary]
  field_simp [hz]
  ring

/-- Envelope theorem for the natural-unit radial perspective: at a stationary
contact, the derivative is the radial partial derivative and does not involve
the derivative of the contact selector. -/
theorem hasDerivAt_stationaryRadialPerspective
    {rho theta : ℝ} {z : ℝ → ℝ} {dz r : ℝ}
    (hz : HasDerivAt z dz r)
    (hzpos : 0 < z r)
    (hRminus : z r - rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hRplus : z r + rho * (r * z r) ∈ Ioo (0 : ℝ) 1)
    (hminus : z r - r * z r ∈ Ioo (0 : ℝ) 1)
    (hplus : z r + r * z r ∈ Ioo (0 : ℝ) 1)
    (hstationary : naturalTriangleLagrangian rho theta (z r) (r * z r) =
      z r * (naturalTriangleKm rho theta (z r) (r * z r) +
        r * naturalTriangleKu rho theta (z r) (r * z r))) :
    HasDerivAt
      (fun s ↦ naturalTriangleLagrangian rho theta (z s) (s * z s) / z s)
      (naturalTriangleKu rho theta (z r) (r * z r)) r := by
  have hk := hasDerivAt_naturalTriangleLagrangian_radialPath
    (rho := rho) (theta := theta) hz
    hRminus hRplus hminus hplus
  have hquot := hasDerivAt_quotientPath hk hz hzpos.ne'
  convert hquot using 1
  exact (stationaryQuotientFirstVariation_eq_ku
    (dz := dz) hzpos.ne' hstationary).symm

end CourtadeKumar
