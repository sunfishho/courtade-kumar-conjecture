import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalConcreteSoundness

/-!
# Semantic bridge for explicit upper-`K` payloads

The historical compact checker reconstructs its payload with `autoPayload`.
For kernel replay we instead serialize that exact data and verify its Boolean
conditions in balanced pieces.  This module keeps the existing analytic
soundness proof while allowing the checked sharp payloads themselves to be
supplied explicitly.
-/

namespace CourtadeKumar
namespace LRUpperKExplicitPayloadSemanticBridge

open LRUpperKReplayCertificate
open LRUpperKHistoricalACValues
open LRUpperKHistoricalThreeCoordinateBase

abbrev Payload := LRUpperKHistoricalACAD.Payload

/-- Soundness of one explicitly supplied sharp payload.  The corner checks
remain separate because their scalar certificates will be balanced
independently. -/
theorem evaluateAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box payload = true)
    (haY0Corner : aCornerCheck 40 48 box (y0AD box).value = true)
    (hcY0Corner : cCornerCheck 40 48 box (y0AD box).value = true)
    (haECorner : aCornerCheck 40 48 box (eAD box).value = true)
    (hcECorner : cCornerCheck 40 48 box (eAD box).value = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (LRUpperKHistoricalEvaluatorAssembly.evaluateAD terms box payload).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (targetChartDerivH coordinate) := by
  have hsharpNodes :=
    LRUpperKHistoricalSharpNodeSoundness.sharpNodeEnclosures_of_checked terms
      hdomain hsharp hcoordinate
      haY0Corner hcY0Corner haECorner hcECorner
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
  have hencloses :=
    LRUpperKHistoricalEvaluatorAssembly.evaluateAD_sound_of_sharp_nodes terms
      hcommon.vLowerPositive hcommon.eLowerPositive
      hcommon.bFlow hcommon.d1 hcommon.g0
      hsharpNodes.aY0 hsharpNodes.aE hsharpNodes.cY0 hsharpNodes.cE
      hcommon.v hcommon.kappa hcommon.delta hcommon.w hcommon.e
  have hjet :=
    LRUpperKHistoricalJetCompatibility.evaluateJet_eq_upperKTarget_of_compatible
      coordinate hePoint hvPoint
  exact
    LRUpperKHistoricalEvaluatorAssembly.contains_upperKTarget_of_encloses
      hencloses hjet

/-- Midpoint certificate assembled from an explicit singleton-center payload
and an explicit whole-box payload. -/
def evaluation (terms : ℕ) (box : CertificateBox)
    (centerPayload derivativePayload : Payload) : MidpointCertificate :=
  let centerNode := LRUpperKHistoricalEvaluatorAssembly.evaluateAD terms
    (centerBox box) centerPayload
  let derivativeNode := LRUpperKHistoricalEvaluatorAssembly.evaluateAD terms
    box derivativePayload
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

/-- The two explicitly checked payloads provide the centered semantic
interface used by the existing open-chart midpoint theorem. -/
theorem centeredEvaluatorSoundness (terms : ℕ) {box : CertificateBox}
    {centerPayload derivativePayload : Payload}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerPayload = true)
    (hcenterAY0 : aCornerCheck 40 48 (centerBox box)
      (y0AD (centerBox box)).value = true)
    (hcenterCY0 : cCornerCheck 40 48 (centerBox box)
      (y0AD (centerBox box)).value = true)
    (hcenterAE : aCornerCheck 40 48 (centerBox box)
      (eAD (centerBox box)).value = true)
    (hcenterCE : cCornerCheck 40 48 (centerBox box)
      (eAD (centerBox box)).value = true)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativePayload = true)
    (hwholeAY0 : aCornerCheck 40 48 box (y0AD box).value = true)
    (hwholeCY0 : cCornerCheck 40 48 box (y0AD box).value = true)
    (hwholeAE : aCornerCheck 40 48 box (eAD box).value = true)
    (hwholeCE : cCornerCheck 40 48 box (eAD box).value = true) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (evaluation terms box centerPayload derivativePayload) := by
  have hcenterDomain :=
    LRUpperKHistoricalConcreteSoundness.openChartBoxCheck_centerBox hdomain
  refine
    { centerValue := ?_
      derivS := ?_
      derivK := ?_
      derivH := ?_ }
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hcenterDomain hcenterSharp
      hcenterAY0 hcenterCY0 hcenterAE hcenterCE hcoordinate
    simpa [evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwholeSharp
      hwholeAY0 hwholeCY0 hwholeAE hwholeCE hcoordinate
    simpa [evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwholeSharp
      hwholeAY0 hwholeCY0 hwholeAE hwholeCE hcoordinate
    simpa [evaluation] using hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwholeSharp
      hwholeAY0 hwholeCY0 hwholeAE hwholeCE hcoordinate
    simpa [evaluation] using hsound.2.2.2

/-- Final leaf theorem for an explicit center/whole payload pair. -/
theorem nonnegative_of_checked (terms : ℕ) {box : CertificateBox}
    {centerPayload derivativePayload : Payload}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerPayload = true)
    (hcenterAY0 : aCornerCheck 40 48 (centerBox box)
      (y0AD (centerBox box)).value = true)
    (hcenterCY0 : cCornerCheck 40 48 (centerBox box)
      (y0AD (centerBox box)).value = true)
    (hcenterAE : aCornerCheck 40 48 (centerBox box)
      (eAD (centerBox box)).value = true)
    (hcenterCE : cCornerCheck 40 48 (centerBox box)
      (eAD (centerBox box)).value = true)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativePayload = true)
    (hwholeAY0 : aCornerCheck 40 48 box (y0AD box).value = true)
    (hwholeCY0 : cCornerCheck 40 48 box (y0AD box).value = true)
    (hwholeAE : aCornerCheck 40 48 box (eAD box).value = true)
    (hwholeCE : cCornerCheck 40 48 box (eAD box).value = true)
    (hevaluation : (evaluation terms box centerPayload derivativePayload).check
      box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hsound := centeredEvaluatorSoundness terms hdomain
    hcenterSharp hcenterAY0 hcenterCY0 hcenterAE hcenterCE
    hwholeSharp hwholeAY0 hwholeCY0 hwholeAE hwholeCE
  exact
    LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
      hdomain hsound hevaluation hcoordinate hrelevant

end LRUpperKExplicitPayloadSemanticBridge
end CourtadeKumar
