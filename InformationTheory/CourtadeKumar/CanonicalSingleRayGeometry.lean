import InformationTheory.CourtadeKumar.CanonicalRadialTangent
import InformationTheory.CourtadeKumar.PerspectiveClosure

/-! Canonical realization of the single-ray phase geometry data. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Once the perspective classification supplies an interior multiplier, its
centered threshold, and a contact ray beyond that threshold, the canonical
radial profile supplies every geometric field required by the single-ray
phase.  The remaining entropy comparison is precisely the isolated LR
theorem. -/
noncomputable def canonicalSingleRayGeometryData
    {alpha : ℝ≥0} {M d E0 theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo rstar 1)
    (hmoment : d = M * r)
    (hentropy : E0 = M /
      canonicalRadialContactZ alpha theta halpha htheta r *
        radialTriangleEntropy r
          (canonicalRadialContactZ alpha theta halpha htheta r))
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    SingleRayGeometryData alpha M d E0 := by
  let c := canonicalRadialProfile alpha theta halpha htheta
  let z := canonicalRadialContactZ alpha theta halpha htheta r
  let b := deriv c r
  let a := c r - r * b
  have hr01 : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨hrstar.1.trans hr.1, hr.2⟩
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr01.1
  refine {
    theta := theta
    c := c
    r := r
    z := z
    a := a
    b := b
    alpha_interior := halpha
    mean_interior := hM
    theta_nonneg := htheta.1.le
    z_pos := hzspec.1.1
    ray_interior := hr01
    contact_before_half := ⟨hzspec.1.1,
      canonicalRadialContactZ_lt_half_after_threshold
        halpha htheta hrstar hcenter hr01 hr.1⟩
    contactProfile := canonicalRadialProfile_contactProfile halpha htheta
    affineMinorant := ?_
    affine_touches := ?_
    radial_contact := ?_
    moment_contact := hmoment
    entropy_contact := ?_
    threshold_eq := hthreshold }
  · exact canonicalRadialTangentMinorant
      halpha htheta hrstar hcenter hr
  · dsimp [a, b]
    ring
  · dsimp [c, z]
    rw [canonicalRadialProfile, if_pos hr01.1]
  · simpa [z] using hentropy

/-- With LR available, the same canonical contact becomes the complete
single-ray phase record consumed by weak duality. -/
noncomputable def canonicalSingleRayPhaseData
    {alpha : ℝ≥0} {M d E0 theta rstar r : ℝ}
    (hlr : SingleRayLRTheorem alpha)
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hM : M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo rstar 1)
    (hmoment : d = M * r)
    (hentropy : E0 = M /
      canonicalRadialContactZ alpha theta halpha htheta r *
        radialTriangleEntropy r
          (canonicalRadialContactZ alpha theta halpha htheta r))
    (hthreshold : E0 =
      (bellmanEnvelope (alpha : ℝ) (M - d) +
        bellmanEnvelope (alpha : ℝ) (M + d)) / 2) :
    SingleRayPhaseData alpha M d E0 :=
  (canonicalSingleRayGeometryData halpha hM htheta hrstar hcenter hr
    hmoment hentropy hthreshold).toPhaseData hlr

end CourtadeKumar
