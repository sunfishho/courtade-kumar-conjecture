import InformationTheory.CourtadeKumar.LRDeterminantUpperKExplicitCornerPayload
import InformationTheory.CourtadeKumar.LRDeterminantUpperKExplicitPayloadSemanticBridge

/-!
# Upper-`K` evaluator with explicit scalar corner certificates

This is the semantic evaluator used by the stack-safe replay.  The sharp
derivative payload and the eight scalar corner endpoint payloads are supplied
as literal certificate data.  Its real target and derivative formulas are
identical to the production historical evaluator.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKExplicitCornerEvaluator

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD
open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKHistoricalEvaluatorAssembly
open LRUpperKHistoricalSharpNodeSoundness
open LRUpperKHistoricalACPartialsSoundness

abbrev SharpPayload := LRUpperKHistoricalACAD.Payload
abbrev CornerPayload := LRUpperKExplicitCornerPayload.Payload

def aY0AD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  let partials := aY0Partials terms box sharp
  { value := LRUpperKExplicitCornerPayload.aCornerI terms box
      (y0AD box).value corners.aY0
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def cY0AD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  let partials := cY0Partials terms box sharp
  { value := LRUpperKExplicitCornerPayload.cCornerI terms box
      (y0AD box).value corners.cY0
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def aEAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  let partials := aEPartials terms box sharp
  { value := LRUpperKExplicitCornerPayload.aCornerI terms box
      (eAD box).value corners.aE
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

def cEAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  let partials := cEPartials terms box sharp
  { value := LRUpperKExplicitCornerPayload.cCornerI terms box
      (eAD box).value corners.cE
    derivS := partials.derivS
    derivK := partials.derivK
    derivChi := partials.derivH }

structure SharpNodeEnclosures (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload)
    (coordinate : CertificatePoint) : Prop where
  aY0 : Encloses (aY0AD terms box sharp corners) (aY0Jet coordinate)
  cY0 : Encloses (cY0AD terms box sharp corners) (cY0Jet coordinate)
  aE : Encloses (aEAD terms box sharp corners) (aEJet coordinate)
  cE : Encloses (cEAD terms box sharp corners) (cEJet coordinate)

theorem sharpNodeEnclosures_of_checked (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload} {corners : CornerPayload}
    {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hcorners : LRUpperKExplicitCornerPayload.Checked box corners)
    (hcoordinate : box.Contains coordinate) :
    SharpNodeEnclosures terms box sharp corners coordinate := by
  have hfacts := LRUpperKHistoricalDomainAdapters.facts_of_checked
    hdomain hsharp hcoordinate
  have hvalid := LRUpperKHistoricalSharpNodeSoundness.partialsValid_of_checked
    hdomain hsharp hcoordinate
  refine
    { aY0 := ?_
      cY0 := ?_
      aE := ?_
      cE := ?_ }
  · have hvalue := LRUpperKExplicitCornerPayload.aCornerI_sound terms
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.y0LowerPhysical
      hfacts.point.y0Physical hfacts.endpoints.y0UpperPhysical
      hfacts.point.sRange hfacts.point.y0Value hcorners.aY0
    have hpartials := aY0Partials_primitive_sound terms hvalid
    simpa [Encloses, aY0AD, aY0Jet, ContainsPartials] using
      And.intro hvalue hpartials
  · have hvalue := LRUpperKExplicitCornerPayload.cCornerI_sound terms
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.y0LowerPhysical
      hfacts.point.y0Physical hfacts.endpoints.y0UpperPhysical
      hfacts.point.sRange hfacts.point.y0Value hcorners.cY0
    have hpartials := cY0Partials_primitive_sound terms hvalid
    simpa [Encloses, cY0AD, cY0Jet, ContainsPartials] using
      And.intro hvalue hpartials
  · have hvalue := LRUpperKExplicitCornerPayload.aCornerI_sound terms
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.eLowerPhysical
      hfacts.point.ePhysical hfacts.endpoints.eUpperPhysical
      hfacts.point.sRange hfacts.point.eValue hcorners.aE
    have hpartials := aEPartials_primitive_sound terms hvalid
    simpa [Encloses, aEAD, aEJet, ContainsPartials] using
      And.intro hvalue hpartials
  · have hvalue := LRUpperKExplicitCornerPayload.cCornerI_sound terms
      hfacts.endpoints.sLoPhysical hfacts.point.sPhysical
      hfacts.endpoints.sHiPhysical hfacts.endpoints.eLowerPhysical
      hfacts.point.ePhysical hfacts.endpoints.eUpperPhysical
      hfacts.point.sRange hfacts.point.eValue hcorners.cE
    have hpartials := cEPartials_primitive_sound terms hvalid
    simpa [Encloses, cEAD, cEJet, ContainsPartials] using
      And.intro hvalue hpartials

/-! ## Explicit-corner composite evaluator -/

def psiAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add
      (sharp.base.g0.evaluate terms (vAD box sharp.base))
      (aY0AD terms box sharp corners))
    (IntervalAD.add
      (IntervalAD.divPositive (aEAD terms box sharp corners)
        (vAD box sharp.base))
      (IntervalAD.mul (kappaAD box sharp.base)
        (wAD terms box sharp.base)))

def baseAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add (cY0AD terms box sharp corners)
      (IntervalAD.divPositive (cEAD terms box sharp corners)
        (vAD box sharp.base)))
    (IntervalAD.mul
      (IntervalAD.add (kappaAD box sharp.base)
        (IntervalAD.mul (IntervalAD.const 4) (deltaAD box sharp.base)))
      (wAD terms box sharp.base))

def evaluateAD (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  historicalAssociationAD
    (bFlowAD terms box sharp.base)
    (baseAD terms box sharp corners)
    (d1AD terms box sharp.base)
    (psiAD terms box sharp corners)
    (eAD box)

theorem psiAD_sound_of_nodes (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload} {corners : CornerPayload}
    {g0Jet aY0Jet' aEJet' vJet kappaJet wJet : Jet3}
    (hvPositive : (0 : ℚ) < (vAD box sharp.base).value.lower)
    (hg0 : Encloses (sharp.base.g0.evaluate terms (vAD box sharp.base)) g0Jet)
    (haY0 : Encloses (aY0AD terms box sharp corners) aY0Jet')
    (haE : Encloses (aEAD terms box sharp corners) aEJet')
    (hv : Encloses (vAD box sharp.base) vJet)
    (hkappa : Encloses (kappaAD box sharp.base) kappaJet)
    (hw : Encloses (wAD terms box sharp.base) wJet) :
    Encloses (psiAD terms box sharp corners)
      (LRUpperKHistoricalEvaluatorAssembly.psiJet
        g0Jet aY0Jet' aEJet' vJet kappaJet wJet) := by
  have haEOver := encloses_divPositive hvPositive haE hv
  have hkappaW := encloses_mul hkappa hw
  have hleft := encloses_add hg0 haY0
  have hright := encloses_add haEOver hkappaW
  simpa [psiAD, LRUpperKHistoricalEvaluatorAssembly.psiJet] using
    encloses_add hleft hright

theorem baseAD_sound_of_nodes (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload} {corners : CornerPayload}
    {cY0Jet' cEJet' vJet kappaJet deltaJet wJet : Jet3}
    (hvPositive : (0 : ℚ) < (vAD box sharp.base).value.lower)
    (hcY0 : Encloses (cY0AD terms box sharp corners) cY0Jet')
    (hcE : Encloses (cEAD terms box sharp corners) cEJet')
    (hv : Encloses (vAD box sharp.base) vJet)
    (hkappa : Encloses (kappaAD box sharp.base) kappaJet)
    (hdelta : Encloses (deltaAD box sharp.base) deltaJet)
    (hw : Encloses (wAD terms box sharp.base) wJet) :
    Encloses (baseAD terms box sharp corners)
      (LRUpperKHistoricalEvaluatorAssembly.baseJet
        cY0Jet' cEJet' vJet kappaJet deltaJet wJet) := by
  let fourJet : Jet3 :=
    { value := 4, derivS := 0, derivK := 0, derivH := 0 }
  have hfour : Encloses (IntervalAD.const 4) fourJet := by
    simpa [Encloses, fourJet] using IntervalAD.contains_const 4
  have hcEOver := encloses_divPositive hvPositive hcE hv
  have hkapPlusDelta := encloses_add hkappa (encloses_mul hfour hdelta)
  have hweighted := encloses_mul hkapPlusDelta hw
  have hleft := encloses_add hcY0 hcEOver
  simpa [baseAD, LRUpperKHistoricalEvaluatorAssembly.baseJet, fourJet] using
    encloses_add hleft hweighted

theorem evaluateAD_sound_of_nodes (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload} {corners : CornerPayload}
    {bJet d1Jet g0Jet aY0Jet' aEJet' cY0Jet' cEJet' vJet
      kappaJet deltaJet wJet eJet : Jet3}
    (hvPositive : (0 : ℚ) < (vAD box sharp.base).value.lower)
    (hePositive : (0 : ℚ) < (eAD box).value.lower)
    (hb : Encloses (bFlowAD terms box sharp.base) bJet)
    (hd1 : Encloses (d1AD terms box sharp.base) d1Jet)
    (hg0 : Encloses (sharp.base.g0.evaluate terms (vAD box sharp.base)) g0Jet)
    (haY0 : Encloses (aY0AD terms box sharp corners) aY0Jet')
    (haE : Encloses (aEAD terms box sharp corners) aEJet')
    (hcY0 : Encloses (cY0AD terms box sharp corners) cY0Jet')
    (hcE : Encloses (cEAD terms box sharp corners) cEJet')
    (hv : Encloses (vAD box sharp.base) vJet)
    (hkappa : Encloses (kappaAD box sharp.base) kappaJet)
    (hdelta : Encloses (deltaAD box sharp.base) deltaJet)
    (hw : Encloses (wAD terms box sharp.base) wJet)
    (he : Encloses (eAD box) eJet) :
    Encloses (evaluateAD terms box sharp corners)
      (LRUpperKHistoricalEvaluatorAssembly.evaluateJet
        bJet d1Jet g0Jet aY0Jet' aEJet' cY0Jet' cEJet'
        vJet kappaJet deltaJet wJet eJet) := by
  have hpsi := psiAD_sound_of_nodes terms hvPositive
    hg0 haY0 haE hv hkappa hw
  have hbase := baseAD_sound_of_nodes terms hvPositive
    hcY0 hcE hv hkappa hdelta hw
  have hresult := historicalAssociationAD_sound hePositive
    hb hbase hd1 hpsi he
  simpa [evaluateAD, LRUpperKHistoricalEvaluatorAssembly.evaluateJet] using
    hresult

/-! ## Genuine-target and midpoint soundness -/

theorem evaluateAD_sound (terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload} {corners : CornerPayload}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hcorners : LRUpperKExplicitCornerPayload.check box corners = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (evaluateAD terms box sharp corners).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (targetChartDerivH coordinate) := by
  have hcornerFacts :=
    LRUpperKExplicitCornerPayload.checked_of_check hcorners
  have hsharpNodes := sharpNodeEnclosures_of_checked terms
    hdomain hsharp hcornerFacts hcoordinate
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
  have hencloses := evaluateAD_sound_of_nodes terms
    hcommon.vLowerPositive hcommon.eLowerPositive
    hcommon.bFlow hcommon.d1 hcommon.g0
    hsharpNodes.aY0 hsharpNodes.aE hsharpNodes.cY0 hsharpNodes.cE
    hcommon.v hcommon.kappa hcommon.delta hcommon.w hcommon.e
  have hjet :=
    LRUpperKHistoricalJetCompatibility.evaluateJet_eq_upperKTarget_of_compatible
      coordinate hePoint hvPoint
  exact LRUpperKHistoricalEvaluatorAssembly.contains_upperKTarget_of_encloses
    hencloses hjet

def evaluation (terms : ℕ) (box : CertificateBox)
    (centerSharp derivativeSharp : SharpPayload)
    (centerCorners derivativeCorners : CornerPayload) : MidpointCertificate :=
  let centerNode := evaluateAD terms (centerBox box) centerSharp centerCorners
  let derivativeNode := evaluateAD terms box derivativeSharp derivativeCorners
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

theorem centeredEvaluatorSoundness (terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerSharp = true)
    (hcenterCorners : LRUpperKExplicitCornerPayload.check
      (centerBox box) centerCorners = true)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeCorners : LRUpperKExplicitCornerPayload.check
      box derivativeCorners = true) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (evaluation terms box centerSharp derivativeSharp
        centerCorners derivativeCorners) := by
  have hcenterDomain :=
    LRUpperKHistoricalConcreteSoundness.openChartBoxCheck_centerBox hdomain
  refine
    { centerValue := ?_
      derivS := ?_
      derivK := ?_
      derivH := ?_ }
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hcenterDomain hcenterSharp
      hcenterCorners hcoordinate
    simpa [evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwholeSharp
      hwholeCorners hcoordinate
    simpa [evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwholeSharp
      hwholeCorners hcoordinate
    simpa [evaluation] using hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwholeSharp
      hwholeCorners hcoordinate
    simpa [evaluation] using hsound.2.2.2

theorem nonnegative_of_checked (terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerSharp = true)
    (hcenterCorners : LRUpperKExplicitCornerPayload.check
      (centerBox box) centerCorners = true)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeCorners : LRUpperKExplicitCornerPayload.check
      box derivativeCorners = true)
    (hevaluation : (evaluation terms box centerSharp derivativeSharp
      centerCorners derivativeCorners).check box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hsound := centeredEvaluatorSoundness terms hdomain
    hcenterSharp hcenterCorners hwholeSharp hwholeCorners
  exact
    LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
      hdomain hsound hevaluation hcoordinate hrelevant

end LRUpperKExplicitCornerEvaluator
end CourtadeKumar
