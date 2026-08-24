import InformationTheory.CourtadeKumar.CanonicalRadialContactSmoothness

/-! Envelope derivative of the canonical radial profile. -/

open Set
open Filter
open scoped NNReal

namespace CourtadeKumar

theorem naturalTriangleLagrangian_radial_eq
    (alpha : ℝ≥0) (theta r z : ℝ) :
    naturalTriangleLagrangian (channelRho (alpha : ℝ)) theta z (r * z) =
      radialNatDifference alpha theta r z := by
  unfold naturalTriangleLagrangian scaledNatEntropy radialNatDifference
    radialNatEntropy
  congr 4 <;> ring

/-- The derivative of the attained canonical profile is its radial partial
derivative.  The derivative of the canonical contact selector cancels by the
stationarity envelope identity. -/
theorem hasDerivAt_canonicalRadialProfile
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (canonicalRadialProfile alpha theta halpha htheta)
      (naturalTriangleKu (channelRho (alpha : ℝ)) theta
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (r * canonicalRadialContactZ alpha theta halpha htheta r) /
          Real.log 2) r := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let zfun : ℝ → ℝ := canonicalRadialContactZ alpha theta halpha htheta
  let z : ℝ := zfun r
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    dsimp [rho]
    exact channelRho_mem_Icc_of_alpha_interior halpha
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := hzspec.1
  have hlogRatio : radialEulerLogRatio rho r z = theta := hzspec.2
  have hzdiff : DifferentiableAt ℝ zfun r :=
    (contDiffAt_canonicalRadialContactZ halpha htheta hr).differentiableAt two_ne_zero
  have hzderiv : HasDerivAt zfun (deriv zfun r) r := hzdiff.hasDerivAt
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hr hz
  have hratio : radialEulerRatio rho r z = theta := by
    rw [radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus]
    exact hlogRatio
  have hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0 :=
    (radial_stationary_iff_ratio hminus hplus).2 hratio
  have hstationary := naturalTriangleLagrangian_euler_at_stationary hstat
  have hRminus' : z - rho * (r * z) ∈ Ioo (0 : ℝ) 1 := by
    convert hRminus using 1 <;> ring
  have hRplus' : z + rho * (r * z) ∈ Ioo (0 : ℝ) 1 := by
    convert hRplus using 1 <;> ring
  have hminus' : z - r * z ∈ Ioo (0 : ℝ) 1 := by
    convert hminus using 1 <;> ring
  have hplus' : z + r * z ∈ Ioo (0 : ℝ) 1 := by
    convert hplus using 1 <;> ring
  have hnat := hasDerivAt_stationaryRadialPerspective
    (rho := rho) (theta := theta) hzderiv hz.1
    (by simpa [z] using hRminus')
    (by simpa [z] using hRplus')
    (by simpa [z] using hminus')
    (by simpa [z] using hplus')
    hstationary
  have hbits := hnat.div_const (Real.log 2)
  have hlocal : canonicalRadialProfile alpha theta halpha htheta =ᶠ[nhds r]
      (fun s ↦ naturalTriangleLagrangian rho theta (zfun s) (s * zfun s) /
        zfun s / Real.log 2) := by
    filter_upwards [lt_mem_nhds hr.1] with s hs
    rw [show canonicalRadialProfile alpha theta halpha htheta s =
        radialTriangleDifference alpha theta s (zfun s) / zfun s by
      simp [canonicalRadialProfile, zfun, hs]]
    rw [radialTriangleDifference_eq_nat]
    rw [← naturalTriangleLagrangian_radial_eq]
    dsimp [rho]
    ring
  have hfinal := hbits.congr_of_eventuallyEq hlocal
  simpa [rho, zfun, z] using hfinal

end CourtadeKumar
