import InformationTheory.CourtadeKumar.LRDeterminantUpperKRoundedExplicitCornerEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantUpperKAutoCornerCorrectness

/-!
# Reusable cached upper-`K` corner-value evaluator

The four monotone `A/C` value hulls are the expensive part of the explicit
corner nodes.  Their derivative intervals are independent sharp bounds.  This
module permits any rational outer hull for each value, then transports the
existing exact-node semantics through componentwise containment.
-/

namespace CourtadeKumar
namespace LRUpperKCachedCornerValues

open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKHistoricalEvaluatorAssembly
open LRUpperKMidpointCoarsening
open LRUpperKDyadicOuterRounding

abbrev SharpPayload := LRUpperKHistoricalACAD.Payload
abbrev CornerPayload := LRUpperKExplicitCornerPayload.Payload

structure Values where
  aY0 : RationalEnclosure
  cY0 : RationalEnclosure
  aE : RationalEnclosure
  cE : RationalEnclosure

/-- Form a monotone corner hull from independently cached scalar enclosures. -/
def cornerHull (lower upper : RationalEnclosure) : RationalEnclosure :=
  { lower := lower.lower, upper := upper.upper }

/-- The eight scalar endpoint hulls from which the four monotone corner
values are assembled.  Keeping these endpoints separate lets generated
replays reuse a scalar value across every leaf which asks for the same exact
`(A/C,s,y)` call. -/
structure ScalarValues where
  aY0Lower : RationalEnclosure
  aY0Upper : RationalEnclosure
  cY0Lower : RationalEnclosure
  cY0Upper : RationalEnclosure
  aELower : RationalEnclosure
  aEUpper : RationalEnclosure
  cELower : RationalEnclosure
  cEUpper : RationalEnclosure

def ScalarValues.assemble (values : ScalarValues) : Values :=
  { aY0 := cornerHull values.aY0Lower values.aY0Upper
    cY0 := cornerHull values.cY0Lower values.cY0Upper
    aE := cornerHull values.aELower values.aEUpper
    cE := cornerHull values.cELower values.cEUpper }

theorem aCornerI_covers_of_scalar_covers (terms : ℕ)
    {box : CertificateBox} {input : RationalEnclosure}
    {payload : LRUpperKExplicitCornerPayload.Pair}
    {lowerValue upperValue : RationalEnclosure}
    (hlower : Covers lowerValue
      (LRUpperKHistoricalACValues.aScalarI terms box.sHi input.lower
        payload.lower))
    (hupper : Covers upperValue
      (LRUpperKHistoricalACValues.aScalarI terms box.sLo input.upper
        payload.upper)) :
    Covers (cornerHull lowerValue upperValue)
      (LRUpperKExplicitCornerPayload.aCornerI terms box input payload) := by
  exact ⟨hlower.1, hupper.2⟩

theorem cCornerI_covers_of_scalar_covers (terms : ℕ)
    {box : CertificateBox} {input : RationalEnclosure}
    {payload : LRUpperKExplicitCornerPayload.Pair}
    {lowerValue upperValue : RationalEnclosure}
    (hlower : Covers lowerValue
      (LRUpperKHistoricalACValues.cScalarI terms box.sHi input.upper
        payload.lower))
    (hupper : Covers upperValue
      (LRUpperKHistoricalACValues.cScalarI terms box.sLo input.lower
        payload.upper)) :
    Covers (cornerHull lowerValue upperValue)
      (LRUpperKExplicitCornerPayload.cCornerI terms box input payload) := by
  exact ⟨hlower.1, hupper.2⟩

structure CoversExact (terms : ℕ) (box : CertificateBox)
    (corners : CornerPayload) (values : Values) : Prop where
  aY0 : Covers values.aY0
    (LRUpperKExplicitCornerPayload.aCornerI terms box
      (LRUpperKReplayCertificate.y0AD box).value corners.aY0)
  cY0 : Covers values.cY0
    (LRUpperKExplicitCornerPayload.cCornerI terms box
      (LRUpperKReplayCertificate.y0AD box).value corners.cY0)
  aE : Covers values.aE
    (LRUpperKExplicitCornerPayload.aCornerI terms box
      (LRUpperKReplayCertificate.eAD box).value corners.aE)
  cE : Covers values.cE
    (LRUpperKExplicitCornerPayload.cCornerI terms box
      (LRUpperKReplayCertificate.eAD box).value corners.cE)

/-- Assemble an exact cached-corner cover from eight independently reusable
outer hulls of the deterministic scalar calls. -/
theorem coversExact_auto (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : ScalarValues)
    (haY0Lower : Covers values.aY0Lower
      (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
        box.sHi (LRUpperKReplayCertificate.y0AD box).value.lower))
    (haY0Upper : Covers values.aY0Upper
      (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
        box.sLo (LRUpperKReplayCertificate.y0AD box).value.upper))
    (hcY0Lower : Covers values.cY0Lower
      (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
        box.sHi (LRUpperKReplayCertificate.y0AD box).value.upper))
    (hcY0Upper : Covers values.cY0Upper
      (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
        box.sLo (LRUpperKReplayCertificate.y0AD box).value.lower))
    (haELower : Covers values.aELower
      (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
        box.sHi (LRUpperKReplayCertificate.eAD box).value.lower))
    (haEUpper : Covers values.aEUpper
      (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
        box.sLo (LRUpperKReplayCertificate.eAD box).value.upper))
    (hcELower : Covers values.cELower
      (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
        box.sHi (LRUpperKReplayCertificate.eAD box).value.upper))
    (hcEUpper : Covers values.cEUpper
      (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
        box.sLo (LRUpperKReplayCertificate.eAD box).value.lower)) :
    CoversExact terms box
      (LRUpperKExplicitCornerPayload.auto sqrtFuel logFuel box)
      values.assemble := by
  refine
    { aY0 := aCornerI_covers_of_scalar_covers terms ?_ ?_
      cY0 := cCornerI_covers_of_scalar_covers terms ?_ ?_
      aE := aCornerI_covers_of_scalar_covers terms ?_ ?_
      cE := cCornerI_covers_of_scalar_covers terms ?_ ?_ }
  · simpa [LRUpperKHistoricalACValues.aAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.aPairAuto] using haY0Lower
  · simpa [LRUpperKHistoricalACValues.aAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.aPairAuto] using haY0Upper
  · simpa [LRUpperKHistoricalACValues.cAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.cPairAuto] using hcY0Lower
  · simpa [LRUpperKHistoricalACValues.cAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.cPairAuto] using hcY0Upper
  · simpa [LRUpperKHistoricalACValues.aAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.aPairAuto] using haELower
  · simpa [LRUpperKHistoricalACValues.aAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.aPairAuto] using haEUpper
  · simpa [LRUpperKHistoricalACValues.cAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.cPairAuto] using hcELower
  · simpa [LRUpperKHistoricalACValues.cAutoI,
      LRUpperKExplicitCornerPayload.auto,
      LRUpperKExplicitCornerPayload.cPairAuto] using hcEUpper

def aY0AD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : Values) : IntervalAD :=
  let partials := LRUpperKHistoricalACAD.aY0Partials
    terms box sharp
  { value := values.aY0
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def cY0AD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : Values) : IntervalAD :=
  let partials := LRUpperKHistoricalACAD.cY0Partials
    terms box sharp
  { value := values.cY0
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def aEAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : Values) : IntervalAD :=
  let partials := LRUpperKHistoricalACAD.aEPartials
    terms box sharp
  { value := values.aE
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def cEAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : Values) : IntervalAD :=
  let partials := LRUpperKHistoricalACAD.cEPartials
    terms box sharp
  { value := values.cE
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

structure SharpNodeEnclosures (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : Values)
    (coordinate : CertificatePoint) : Prop where
  aY0 : Encloses (aY0AD terms box sharp values)
    (LRUpperKHistoricalSharpNodeSoundness.aY0Jet coordinate)
  cY0 : Encloses (cY0AD terms box sharp values)
    (LRUpperKHistoricalSharpNodeSoundness.cY0Jet coordinate)
  aE : Encloses (aEAD terms box sharp values)
    (LRUpperKHistoricalSharpNodeSoundness.aEJet coordinate)
  cE : Encloses (cEAD terms box sharp values)
    (LRUpperKHistoricalSharpNodeSoundness.cEJet coordinate)

theorem aY0AD_covers (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) (values : Values)
    (hcovers : CoversExact terms box corners values) :
    ADCovers (aY0AD terms box sharp values)
      (LRUpperKExplicitCornerEvaluator.aY0AD terms box sharp corners) := by
  simpa [ADCovers, Covers, aY0AD,
    LRUpperKExplicitCornerEvaluator.aY0AD] using hcovers.aY0

theorem cY0AD_covers (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) (values : Values)
    (hcovers : CoversExact terms box corners values) :
    ADCovers (cY0AD terms box sharp values)
      (LRUpperKExplicitCornerEvaluator.cY0AD terms box sharp corners) := by
  simpa [ADCovers, Covers, cY0AD,
    LRUpperKExplicitCornerEvaluator.cY0AD] using hcovers.cY0

theorem aEAD_covers (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) (values : Values)
    (hcovers : CoversExact terms box corners values) :
    ADCovers (aEAD terms box sharp values)
      (LRUpperKExplicitCornerEvaluator.aEAD terms box sharp corners) := by
  simpa [ADCovers, Covers, aEAD,
    LRUpperKExplicitCornerEvaluator.aEAD] using hcovers.aE

theorem cEAD_covers (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) (values : Values)
    (hcovers : CoversExact terms box corners values) :
    ADCovers (cEAD terms box sharp values)
      (LRUpperKExplicitCornerEvaluator.cEAD terms box sharp corners) := by
  simpa [ADCovers, Covers, cEAD,
    LRUpperKExplicitCornerEvaluator.cEAD] using hcovers.cE

theorem sharpNodeEnclosures_of_checked (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload}
    {corners : CornerPayload} {values : Values}
    {coordinate : CertificatePoint}
    (hdomain : LRUpperKReplayCertificate.openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hcorners : LRUpperKExplicitCornerPayload.Checked box corners)
    (hcovers : CoversExact terms box corners values)
    (hcoordinate : box.Contains coordinate) :
    SharpNodeEnclosures terms box sharp values coordinate := by
  have hexact :=
    LRUpperKExplicitCornerEvaluator.sharpNodeEnclosures_of_checked terms
      hdomain hsharp hcorners hcoordinate
  exact
    { aY0 := encloses_of_covers
        (aY0AD_covers terms box sharp corners values hcovers) hexact.aY0
      cY0 := encloses_of_covers
        (cY0AD_covers terms box sharp corners values hcovers) hexact.cY0
      aE := encloses_of_covers
        (aEAD_covers terms box sharp corners values hcovers) hexact.aE
      cE := encloses_of_covers
        (cEAD_covers terms box sharp corners values hcovers) hexact.cE }

abbrev Nodes := LRUpperKExplicitEvaluatorNodes.Payload

def materialize (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload)
    (values : Values) : Nodes :=
  { (LRUpperKExplicitEvaluatorNodes.materialize terms box sharp corners) with
    aY0 := aY0AD terms box sharp values
    aE := aEAD terms box sharp values
    cY0 := cY0AD terms box sharp values
    cE := cEAD terms box sharp values }

def nodes (bits terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload)
    (values : Values) : Nodes :=
  LRUpperKRoundedEvaluatorArithmetic.outerNodes bits
    (materialize terms box sharp corners values)

def evaluateAD (bits terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload)
    (values : Values) : IntervalAD :=
  LRUpperKRoundedEvaluatorArithmetic.evaluateAD bits
    (nodes bits terms box sharp corners values)

theorem evaluateAD_sound_of_sharp_nodes (bits terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload}
    {corners : CornerPayload} {values : Values}
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hsharpNodes : SharpNodeEnclosures terms box sharp values coordinate)
    (hvRounded : (0 : ℚ) <
      (nodes bits terms box sharp corners values).v.value.lower)
    (heRounded : (0 : ℚ) <
      (nodes bits terms box sharp corners values).e.value.lower) :
    (evaluateAD bits terms box sharp corners values).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (LRUpperKReplayCertificate.targetChartDerivS coordinate)
      (LRUpperKReplayCertificate.targetChartDerivK coordinate)
      (LRUpperKHistoricalThreeCoordinateBase.targetChartDerivH coordinate) := by
  have hcommon :=
    LRUpperKHistoricalCommonComponents.commonComponentsAt_of_checked terms
      hsharp hcoordinate
  have hePoint :
      0 < lrCertificateE
        (LRUpperKHistoricalTargetJetBridge.rawPoint coordinate) := by
    simpa [LRUpperKHistoricalTargetJetBridge.rawPoint,
      LRUpperKHistoricalCommonComponents.rawAt] using
      hcommon.ePointPositive
  have hvPoint :
      0 < lrCertificateV
        (LRUpperKHistoricalTargetJetBridge.rawPoint coordinate) := by
    simpa [LRUpperKHistoricalTargetJetBridge.rawPoint,
      LRUpperKHistoricalCommonComponents.rawAt] using
      hcommon.vPointPositive
  have hb : Encloses
      (nodes bits terms box sharp corners values).bFlow
        (LRUpperKHistoricalCommonComponents.bFlowJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.bFlow
  have hd1 : Encloses
      (nodes bits terms box sharp corners values).d1
        (LRUpperKHistoricalCommonComponents.d1Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.d1
  have hg0 : Encloses
      (nodes bits terms box sharp corners values).g0
        (LRUpperKHistoricalCommonComponents.g0Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.g0
  have haY0 : Encloses
      (nodes bits terms box sharp corners values).aY0
        (LRUpperKHistoricalSharpNodeSoundness.aY0Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.aY0
  have haE : Encloses
      (nodes bits terms box sharp corners values).aE
        (LRUpperKHistoricalSharpNodeSoundness.aEJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.aE
  have hcY0 : Encloses
      (nodes bits terms box sharp corners values).cY0
        (LRUpperKHistoricalSharpNodeSoundness.cY0Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.cY0
  have hcE : Encloses
      (nodes bits terms box sharp corners values).cE
        (LRUpperKHistoricalSharpNodeSoundness.cEJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.cE
  have hv : Encloses
      (nodes bits terms box sharp corners values).v
        (LRUpperKHistoricalCommonComponents.vJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.v
  have hkappa : Encloses
      (nodes bits terms box sharp corners values).kappa
        (LRUpperKHistoricalCommonComponents.kappaJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.kappa
  have hdelta : Encloses
      (nodes bits terms box sharp corners values).delta
        (LRUpperKHistoricalCommonComponents.deltaJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.delta
  have hw : Encloses
      (nodes bits terms box sharp corners values).w
        (LRUpperKHistoricalCommonComponents.wJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.w
  have he : Encloses
      (nodes bits terms box sharp corners values).e
        (LRUpperKHistoricalCommonComponents.eJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.e
  have hencloses :=
    LRUpperKRoundedEvaluatorArithmetic.evaluateAD_sound_of_nodes
      (bits := bits) hvRounded heRounded
      hb hd1 hg0 haY0 haE hcY0 hcE hv hkappa hdelta hw he
  have hjet :=
    LRUpperKHistoricalJetCompatibility.evaluateJet_eq_upperKTarget_of_compatible
      coordinate hePoint hvPoint
  exact LRUpperKHistoricalEvaluatorAssembly.contains_upperKTarget_of_encloses
    hencloses hjet

theorem evaluateAD_sound (bits terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload}
    {corners : CornerPayload} {values : Values}
    (hdomain : LRUpperKReplayCertificate.openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hcorners : LRUpperKExplicitCornerPayload.check box corners = true)
    (hvalues : CoversExact terms box corners values)
    (hvRounded : (0 : ℚ) <
      (nodes bits terms box sharp corners values).v.value.lower)
    (heRounded : (0 : ℚ) <
      (nodes bits terms box sharp corners values).e.value.lower)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (evaluateAD bits terms box sharp corners values).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (LRUpperKReplayCertificate.targetChartDerivS coordinate)
      (LRUpperKReplayCertificate.targetChartDerivK coordinate)
      (LRUpperKHistoricalThreeCoordinateBase.targetChartDerivH coordinate) := by
  have hcornerFacts :=
    LRUpperKExplicitCornerPayload.checked_of_check hcorners
  have hsharpNodes := sharpNodeEnclosures_of_checked terms
    hdomain hsharp hcornerFacts hvalues hcoordinate
  exact evaluateAD_sound_of_sharp_nodes bits terms hsharp
    hcoordinate hsharpNodes hvRounded heRounded

def evaluation (bits terms : ℕ) (box : CertificateBox)
    (centerSharp derivativeSharp : SharpPayload)
    (centerCorners derivativeCorners : CornerPayload)
    (centerValues derivativeValues : Values) : MidpointCertificate :=
  let centerNode := evaluateAD bits terms
    (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
    centerSharp centerCorners centerValues
  let derivativeNode := evaluateAD bits terms box
    derivativeSharp derivativeCorners derivativeValues
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

theorem centeredEvaluatorSoundness (bits terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    {centerValues derivativeValues : Values}
    (hdomain : LRUpperKReplayCertificate.openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp = true)
    (hcenterCorners : LRUpperKExplicitCornerPayload.check
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerCorners = true)
    (hcenterValues : CoversExact terms
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerCorners centerValues)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeCorners : LRUpperKExplicitCornerPayload.check box
      derivativeCorners = true)
    (hwholeValues : CoversExact terms box derivativeCorners derivativeValues)
    (hcenterV : (0 : ℚ) <
      (nodes bits terms
        (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp centerCorners centerValues).v.value.lower)
    (hcenterE : (0 : ℚ) <
      (nodes bits terms
        (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp centerCorners centerValues).e.value.lower)
    (hwholeV : (0 : ℚ) <
      (nodes bits terms box derivativeSharp derivativeCorners
        derivativeValues).v.value.lower)
    (hwholeE : (0 : ℚ) <
      (nodes bits terms box derivativeSharp derivativeCorners
        derivativeValues).e.value.lower) :
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
      hcenterSharp hcenterCorners hcenterValues hcenterV hcenterE hcoordinate
    simpa [evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeCorners hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeCorners hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeCorners hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.2.2

theorem nonnegative_of_checked (bits terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    {centerValues derivativeValues : Values}
    (hdomain : LRUpperKReplayCertificate.openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp = true)
    (hcenterCorners : LRUpperKExplicitCornerPayload.check
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerCorners = true)
    (hcenterValues : CoversExact terms
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerCorners centerValues)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeCorners : LRUpperKExplicitCornerPayload.check box
      derivativeCorners = true)
    (hwholeValues : CoversExact terms box derivativeCorners derivativeValues)
    (hcenterV : (0 : ℚ) <
      (nodes bits terms
        (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp centerCorners centerValues).v.value.lower)
    (hcenterE : (0 : ℚ) <
      (nodes bits terms
        (LRUpperKHistoricalThreeCoordinateBase.centerBox box)
        centerSharp centerCorners centerValues).e.value.lower)
    (hwholeV : (0 : ℚ) <
      (nodes bits terms box derivativeSharp derivativeCorners
        derivativeValues).v.value.lower)
    (hwholeE : (0 : ℚ) <
      (nodes bits terms box derivativeSharp derivativeCorners
        derivativeValues).e.value.lower)
    (hevaluation :
      (evaluation bits terms box centerSharp derivativeSharp
        centerCorners derivativeCorners centerValues derivativeValues).check
          box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : LRUpperKReplayCertificate.CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hsound := centeredEvaluatorSoundness bits terms
    hdomain hcenterSharp hcenterCorners hcenterValues
    hwholeSharp hwholeCorners hwholeValues
    hcenterV hcenterE hwholeV hwholeE
  exact
    LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
      hdomain hsound hevaluation hcoordinate hrelevant

end LRUpperKCachedCornerValues
end CourtadeKumar
