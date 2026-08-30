import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedCornerValues
import InformationTheory.CourtadeKumar.LRDeterminantUpperKPointCache

/-!
# Point-cached upper-`K` corner values

Eight endpoint enclosures are justified directly from shared `Q/Q'` point
certificates.  Analytic monotonicity then promotes them to the same four
corner hulls used by the rounded evaluator, without reconstructing any
interval-AD scalar payload.
-/

namespace CourtadeKumar
namespace LRUpperKPointCachedCornerValues

open Set
open LRUpperKReplayCertificate
open LRUpperKHistoricalEvaluatorAssembly
open LRUpperKHistoricalSharpNodeSoundness
open LRUpperKHistoricalACPartialsSoundness

abbrev ScalarValues := LRUpperKCachedCornerValues.ScalarValues
abbrev Values := LRUpperKCachedCornerValues.Values
abbrev SharpPayload := LRUpperKCachedCornerValues.SharpPayload
abbrev CornerPayload := LRUpperKCachedCornerValues.CornerPayload

structure EndpointSound (box : CertificateBox)
    (values : ScalarValues) : Prop where
  aY0Lower : values.aY0Lower.Contains
    (aPrimitive (box.sHi : ℝ) ((y0AD box).value.lower : ℝ))
  aY0Upper : values.aY0Upper.Contains
    (aPrimitive (box.sLo : ℝ) ((y0AD box).value.upper : ℝ))
  cY0Lower : values.cY0Lower.Contains
    (cPrimitive (box.sHi : ℝ) ((y0AD box).value.upper : ℝ))
  cY0Upper : values.cY0Upper.Contains
    (cPrimitive (box.sLo : ℝ) ((y0AD box).value.lower : ℝ))
  aELower : values.aELower.Contains
    (aPrimitive (box.sHi : ℝ) ((eAD box).value.lower : ℝ))
  aEUpper : values.aEUpper.Contains
    (aPrimitive (box.sLo : ℝ) ((eAD box).value.upper : ℝ))
  cELower : values.cELower.Contains
    (cPrimitive (box.sHi : ℝ) ((eAD box).value.upper : ℝ))
  cEUpper : values.cEUpper.Contains
    (cPrimitive (box.sLo : ℝ) ((eAD box).value.lower : ℝ))

theorem a_cornerHull_sound
    {box : CertificateBox} {input : RationalEnclosure}
    {lowerValue upperValue : RationalEnclosure} {s y : ℝ}
    (hsLo : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hyLo : (input.lower : ℝ) ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : (input.upper : ℝ) ∈ Ico (0 : ℝ) 1)
    (hsRange : (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ))
    (hyRange : input.Contains y)
    (hlower : lowerValue.Contains
      (aPrimitive (box.sHi : ℝ) (input.lower : ℝ)))
    (hupper : upperValue.Contains
      (aPrimitive (box.sLo : ℝ) (input.upper : ℝ))) :
    (LRUpperKCachedCornerValues.cornerHull lowerValue upperValue).Contains
      (aPrimitive s y) := by
  have hcorners := aPrimitive_corner_bounds hsLo hs hsHi
    hyLo hy hyHi hsRange.1 hsRange.2 hyRange.1 hyRange.2
  exact ⟨hlower.1.trans hcorners.1, hcorners.2.trans hupper.2⟩

theorem c_cornerHull_sound
    {box : CertificateBox} {input : RationalEnclosure}
    {lowerValue upperValue : RationalEnclosure} {s y : ℝ}
    (hsLo : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hsHi : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hyLo : (input.lower : ℝ) ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hyHi : (input.upper : ℝ) ∈ Ico (0 : ℝ) 1)
    (hsRange : (box.sLo : ℝ) ≤ s ∧ s ≤ (box.sHi : ℝ))
    (hyRange : input.Contains y)
    (hlower : lowerValue.Contains
      (cPrimitive (box.sHi : ℝ) (input.upper : ℝ)))
    (hupper : upperValue.Contains
      (cPrimitive (box.sLo : ℝ) (input.lower : ℝ))) :
    (LRUpperKCachedCornerValues.cornerHull lowerValue upperValue).Contains
      (cPrimitive s y) := by
  have hcorners := cPrimitive_corner_bounds hsLo hs hsHi
    hyLo hy hyHi hsRange.1 hsRange.2 hyRange.1 hyRange.2
  exact ⟨hlower.1.trans hcorners.1, hcorners.2.trans hupper.2⟩

theorem sharpNodeEnclosures_of_checked (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload}
    {scalarValues : ScalarValues} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hvalues : EndpointSound box scalarValues)
    (hcoordinate : box.Contains coordinate) :
    LRUpperKCachedCornerValues.SharpNodeEnclosures terms box sharp
      scalarValues.assemble coordinate := by
  have hfacts := LRUpperKHistoricalDomainAdapters.facts_of_checked
    hdomain hsharp hcoordinate
  have hvalid := partialsValid_of_checked hdomain hsharp hcoordinate
  refine
    { aY0 := ?_
      cY0 := ?_
      aE := ?_
      cE := ?_ }
  · have hvalue := a_cornerHull_sound
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.y0LowerPhysical
      hfacts.point.y0Physical hfacts.endpoints.y0UpperPhysical
      hfacts.point.sRange hfacts.point.y0Value
      hvalues.aY0Lower hvalues.aY0Upper
    have hpartials := aY0Partials_primitive_sound terms hvalid
    simpa [Encloses, LRUpperKCachedCornerValues.aY0AD,
      LRUpperKCachedCornerValues.ScalarValues.assemble,
      aY0Jet, ContainsPartials] using And.intro hvalue hpartials
  · have hvalue := c_cornerHull_sound
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.y0LowerPhysical
      hfacts.point.y0Physical hfacts.endpoints.y0UpperPhysical
      hfacts.point.sRange hfacts.point.y0Value
      hvalues.cY0Lower hvalues.cY0Upper
    have hpartials := cY0Partials_primitive_sound terms hvalid
    simpa [Encloses, LRUpperKCachedCornerValues.cY0AD,
      LRUpperKCachedCornerValues.ScalarValues.assemble,
      cY0Jet, ContainsPartials] using And.intro hvalue hpartials
  · have hvalue := a_cornerHull_sound
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.eLowerPhysical
      hfacts.point.ePhysical hfacts.endpoints.eUpperPhysical
      hfacts.point.sRange hfacts.point.eValue
      hvalues.aELower hvalues.aEUpper
    have hpartials := aEPartials_primitive_sound terms hvalid
    simpa [Encloses, LRUpperKCachedCornerValues.aEAD,
      LRUpperKCachedCornerValues.ScalarValues.assemble,
      aEJet, ContainsPartials] using And.intro hvalue hpartials
  · have hvalue := c_cornerHull_sound
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.eLowerPhysical
      hfacts.point.ePhysical hfacts.endpoints.eUpperPhysical
      hfacts.point.sRange hfacts.point.eValue
      hvalues.cELower hvalues.cEUpper
    have hpartials := cEPartials_primitive_sound terms hvalid
    simpa [Encloses, LRUpperKCachedCornerValues.cEAD,
      LRUpperKCachedCornerValues.ScalarValues.assemble,
      cEJet, ContainsPartials] using And.intro hvalue hpartials

theorem evaluateAD_sound (bits terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload}
    {corners : CornerPayload} {scalarValues : ScalarValues}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hvalues : EndpointSound box scalarValues)
    (hvRounded : (0 : ℚ) <
      (LRUpperKCachedCornerValues.nodes bits terms box sharp corners
        scalarValues.assemble).v.value.lower)
    (heRounded : (0 : ℚ) <
      (LRUpperKCachedCornerValues.nodes bits terms box sharp corners
        scalarValues.assemble).e.value.lower)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (LRUpperKCachedCornerValues.evaluateAD bits terms box sharp corners
      scalarValues.assemble).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (LRUpperKHistoricalThreeCoordinateBase.targetChartDerivH coordinate) := by
  have hnodes := sharpNodeEnclosures_of_checked terms
    hdomain hsharp hvalues hcoordinate
  exact LRUpperKCachedCornerValues.evaluateAD_sound_of_sharp_nodes
    bits terms hsharp hcoordinate hnodes hvRounded heRounded

def evaluation (bits terms : ℕ) (box : CertificateBox)
    (centerSharp derivativeSharp : SharpPayload)
    (centerCorners derivativeCorners : CornerPayload)
    (centerValues derivativeValues : ScalarValues) : MidpointCertificate :=
  LRUpperKCachedCornerValues.evaluation bits terms box
    centerSharp derivativeSharp centerCorners derivativeCorners
    centerValues.assemble derivativeValues.assemble

theorem centeredEvaluatorSoundness (bits terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    {centerValues derivativeValues : ScalarValues}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp = true)
    (hcenterValues : EndpointSound
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box) centerValues)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeValues : EndpointSound box derivativeValues)
    (hcenterV : (0 : ℚ) <
      (LRUpperKCachedCornerValues.nodes bits terms
        (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp centerCorners centerValues.assemble).v.value.lower)
    (hcenterE : (0 : ℚ) <
      (LRUpperKCachedCornerValues.nodes bits terms
        (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp centerCorners centerValues.assemble).e.value.lower)
    (hwholeV : (0 : ℚ) <
      (LRUpperKCachedCornerValues.nodes bits terms box derivativeSharp
        derivativeCorners derivativeValues.assemble).v.value.lower)
    (hwholeE : (0 : ℚ) <
      (LRUpperKCachedCornerValues.nodes bits terms box derivativeSharp
        derivativeCorners derivativeValues.assemble).e.value.lower) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (evaluation bits terms box centerSharp derivativeSharp
        centerCorners derivativeCorners centerValues derivativeValues) := by
  have hcenterDomain :=
    LRUpperKHistoricalConcreteSoundness.openChartBoxCheck_centerBox hdomain
  refine
    { centerValue := ?_
      derivS := ?_
      derivK := ?_
      derivH := ?_ }
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hcenterDomain
      hcenterSharp hcenterValues hcenterV hcenterE hcoordinate
    simpa [evaluation, LRUpperKCachedCornerValues.evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation, LRUpperKCachedCornerValues.evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation, LRUpperKCachedCornerValues.evaluation] using
      hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation, LRUpperKCachedCornerValues.evaluation] using
      hsound.2.2.2

end LRUpperKPointCachedCornerValues
end CourtadeKumar
