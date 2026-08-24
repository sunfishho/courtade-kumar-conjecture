import InformationTheory.CourtadeKumar.CanonicalRadialSlopeEndpoint

/-! The canonical centered contact supplies the global radial chord. -/

open Set
open scoped NNReal

namespace CourtadeKumar

theorem canonicalRadialSlopeVShape
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    RadialSlopeVShape
      (canonicalRadialProfile alpha theta halpha htheta) rstar := by
  constructor
  · exact (strictAntiOn_radialProfileSlope_before_threshold
      halpha htheta hrstar hcenter).antitoneOn
  · exact monotoneOn_radialProfileSlope_after_threshold_closed
      halpha htheta hrstar hcenter

theorem canonicalRadialChordSupport
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    RadialChordSupport
      (canonicalRadialProfile alpha theta halpha htheta) rstar := by
  exact radialChordSupport_of_slopeVShape hrstar
    (canonicalRadialProfile_zero alpha theta halpha htheta)
    (canonicalRadialSlopeVShape halpha htheta hrstar hcenter)

theorem canonicalCenteredTriangleAffineSupport
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    TriangleAffineSupport alpha theta 0
      (canonicalRadialProfile alpha theta halpha htheta rstar / rstar) := by
  exact triangleAffineSupport_of_radialChord
    (canonicalRadialProfile_contactProfile halpha htheta)
    (canonicalRadialChordSupport halpha htheta hrstar hcenter)

theorem canonicalRadialChord_centered_value
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    canonicalRadialProfile alpha theta halpha htheta rstar =
      2 * radialTriangleDifference alpha theta rstar (1 / 2) := by
  exact canonicalRadialProfile_centeredContact
    halpha htheta hrstar hcenter

end CourtadeKumar
