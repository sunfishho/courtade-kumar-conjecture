import InformationTheory.CourtadeKumar.CanonicalRadialProfileRightConvexity
import InformationTheory.CourtadeKumar.RadialChordSlope

/-! Increase of the radial profile slope after the centered contact. -/

open Set
open scoped NNReal

namespace CourtadeKumar

theorem radialProfileSlopeNumerator_pos_after_threshold
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo rstar 1) :
    0 < r * deriv (canonicalRadialProfile alpha theta halpha htheta) r -
      canonicalRadialProfile alpha theta halpha htheta r := by
  let c := canonicalRadialProfile alpha theta halpha htheta
  have hconv := strictConvexOn_canonicalRadialProfile_after_threshold
    halpha htheta hrstar hcenter
  have hx : rstar ∈ Ico rstar 1 := ⟨le_rfl, hrstar.2⟩
  have hy : r ∈ Ico rstar 1 := ⟨hr.1.le, hr.2⟩
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hrstar.1.trans hr.1, hr.2⟩
  have hcstar0 := hasDerivAt_canonicalRadialProfile halpha htheta hrstar
  have hcr0 := hasDerivAt_canonicalRadialProfile halpha htheta hr01
  have hcstar : HasDerivAt c (deriv c rstar) rstar := by
    exact hcstar0.congr_deriv hcstar0.deriv.symm
  have hcr : HasDerivAt c (deriv c r) r := by
    exact hcr0.congr_deriv hcr0.deriv.symm
  have hleft : deriv c rstar < slope c rstar r :=
    hconv.lt_slope_of_hasDerivAt hx hy hr.1 hcstar
  have hright : slope c rstar r < deriv c r :=
    hconv.slope_lt_of_hasDerivAt hx hy hr.1 hcr
  rw [slope_def_field] at hleft hright
  have hright' := (div_lt_iff₀ (sub_pos.mpr hr.1)).1 hright
  have htangent := canonicalRadialProfile_centered_tangent
    halpha htheta hrstar hcenter
  have hderivGap : 0 < rstar * (deriv c r - deriv c rstar) :=
    mul_pos hrstar.1 (sub_pos.mpr (hleft.trans hright))
  dsimp [c] at hright' htangent hderivGap ⊢
  nlinarith

theorem deriv_radialProfileSlope_pos_after_threshold
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo rstar 1) :
    0 < deriv (radialProfileSlope
      (canonicalRadialProfile alpha theta halpha htheta)) r := by
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hrstar.1.trans hr.1, hr.2⟩
  have hc0 := hasDerivAt_canonicalRadialProfile halpha htheta hr01
  have hc : HasDerivAt
      (canonicalRadialProfile alpha theta halpha htheta)
      (deriv (canonicalRadialProfile alpha theta halpha htheta) r) r :=
    hc0.congr_deriv hc0.deriv.symm
  have hderiv := hasDerivAt_radialProfileSlope hr01.1.ne'
    hc
  rw [hderiv.deriv]
  exact div_pos
    (radialProfileSlopeNumerator_pos_after_threshold
      halpha htheta hrstar hcenter hr)
    (sq_pos_of_pos hr01.1)

theorem strictMonoOn_radialProfileSlope_after_threshold
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    StrictMonoOn (radialProfileSlope
      (canonicalRadialProfile alpha theta halpha htheta))
      (Ico rstar 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico rstar 1)
  · intro r hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨hrstar.1.trans_le hr.1, hr.2⟩
    exact (hasDerivAt_radialProfileSlope hr01.1.ne'
      (hasDerivAt_canonicalRadialProfile halpha htheta hr01)).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ico] at hr
    exact deriv_radialProfileSlope_pos_after_threshold
      halpha htheta hrstar hcenter hr

end CourtadeKumar
