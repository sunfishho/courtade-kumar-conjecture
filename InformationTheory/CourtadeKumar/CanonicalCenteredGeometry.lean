import InformationTheory.CourtadeKumar.CanonicalRadialChord
import InformationTheory.CourtadeKumar.CenteredPhaseTOP

/-! Canonical realization of the centered phase geometry data. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Once the scalar entropy contact chooses an interior multiplier and its
centered threshold, the canonical radial profile supplies every geometric
field needed by the corrected TOP phase. -/
noncomputable def canonicalCenteredEndpointGeometryData
    {alpha : ℝ≥0} {M d E0 theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hd : 0 < d)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hshape : d / M ≤ rstar)
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hentropy : E0 =
      2 * d / rstar * radialTriangleEntropy rstar (1 / 2))
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    CenteredEndpointGeometryData alpha M d E0 where
  theta := theta
  c := canonicalRadialProfile alpha theta halpha htheta
  rstar := rstar
  alpha_interior := halpha
  mean_interior := hM
  displacement_pos := hd
  rstar_interior := hrstar
  phase_shape := hshape
  theta_nonneg := htheta.1.le
  contactProfile := canonicalRadialProfile_contactProfile halpha htheta
  chordSupport := canonicalRadialChordSupport
    halpha htheta hrstar hcenter
  centered_contact := canonicalRadialChord_centered_value
    halpha htheta hrstar hcenter
  entropy_contact := hentropy
  threshold_eq := hthreshold

/-- The same canonical data, upgraded immediately through corrected TOP to
the complete centered phase record consumed by weak duality. -/
noncomputable def canonicalCenteredEndpointPhaseData
    {alpha : ℝ≥0} {M d E0 theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hd : 0 < d)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hshape : d / M ≤ rstar)
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hentropy : E0 =
      2 * d / rstar * radialTriangleEntropy rstar (1 / 2))
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    CenteredEndpointPhaseData alpha M d E0 :=
  (canonicalCenteredEndpointGeometryData halpha hM hd hrstar hshape
    htheta hcenter hentropy hthreshold).toPhaseData

end CourtadeKumar
