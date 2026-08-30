import InformationTheory.CourtadeKumar.LRDeterminantUpperKRoundedEvaluatorArithmetic
import InformationTheory.CourtadeKumar.LRDeterminantUpperKExplicitCornerEvaluator

/-!
# Sound rounded explicit-corner evaluator

This adapter rounds all twelve checked semantic nodes and every subsequent
arithmetic operation.  Its proof reuses the existing analytic node theorems;
rounding contributes only generic outer-containment lemmas.
-/

namespace CourtadeKumar
namespace LRUpperKRoundedExplicitCornerEvaluator

open LRUpperKReplayCertificate
open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKHistoricalEvaluatorAssembly
open LRUpperKMidpointCoarsening
open LRUpperKDyadicOuterRounding

abbrev SharpPayload := LRUpperKHistoricalACAD.Payload
abbrev CornerPayload := LRUpperKExplicitCornerPayload.Payload
abbrev Nodes := LRUpperKExplicitEvaluatorNodes.Payload

def nodes (bits terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : Nodes :=
  LRUpperKRoundedEvaluatorArithmetic.outerNodes bits
    (LRUpperKExplicitEvaluatorNodes.materialize terms box sharp corners)

def evaluateAD (bits terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (corners : CornerPayload) : IntervalAD :=
  LRUpperKRoundedEvaluatorArithmetic.evaluateAD bits
    (nodes bits terms box sharp corners)

theorem evaluateAD_sound (bits terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload} {corners : CornerPayload}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hcorners : LRUpperKExplicitCornerPayload.check box corners = true)
    (hvRounded : (0 : ℚ) <
      (nodes bits terms box sharp corners).v.value.lower)
    (heRounded : (0 : ℚ) <
      (nodes bits terms box sharp corners).e.value.lower)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (evaluateAD bits terms box sharp corners).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (targetChartDerivH coordinate) := by
  have hcornerFacts :=
    LRUpperKExplicitCornerPayload.checked_of_check hcorners
  have hsharpNodes :=
    LRUpperKExplicitCornerEvaluator.sharpNodeEnclosures_of_checked terms
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
  have hb := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.bFlow
  have hd1 := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.d1
  have hg0 := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.g0
  have haY0 := encloses_of_covers
    (outerIntervalAD_covers bits _) hsharpNodes.aY0
  have haE := encloses_of_covers
    (outerIntervalAD_covers bits _) hsharpNodes.aE
  have hcY0 := encloses_of_covers
    (outerIntervalAD_covers bits _) hsharpNodes.cY0
  have hcE := encloses_of_covers
    (outerIntervalAD_covers bits _) hsharpNodes.cE
  have hv := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.v
  have hkappa := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.kappa
  have hdelta := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.delta
  have hw := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.w
  have he := encloses_of_covers
    (outerIntervalAD_covers bits _) hcommon.e
  have hencloses :=
    LRUpperKRoundedEvaluatorArithmetic.evaluateAD_sound_of_nodes
      (bits := bits) hvRounded heRounded
      hb hd1 hg0 haY0 haE hcY0 hcE hv hkappa hdelta hw he
  have hjet :=
    LRUpperKHistoricalJetCompatibility.evaluateJet_eq_upperKTarget_of_compatible
      coordinate hePoint hvPoint
  exact LRUpperKHistoricalEvaluatorAssembly.contains_upperKTarget_of_encloses
    hencloses hjet

def evaluation (bits terms : ℕ) (box : CertificateBox)
    (centerSharp derivativeSharp : SharpPayload)
    (centerCorners derivativeCorners : CornerPayload) : MidpointCertificate :=
  let centerNode := evaluateAD bits terms (centerBox box)
    centerSharp centerCorners
  let derivativeNode := evaluateAD bits terms box
    derivativeSharp derivativeCorners
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

theorem centeredEvaluatorSoundness (bits terms : ℕ)
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
    (hcenterV : (0 : ℚ) <
      (nodes bits terms (centerBox box) centerSharp centerCorners).v.value.lower)
    (hcenterE : (0 : ℚ) <
      (nodes bits terms (centerBox box) centerSharp centerCorners).e.value.lower)
    (hwholeV : (0 : ℚ) <
      (nodes bits terms box derivativeSharp derivativeCorners).v.value.lower)
    (hwholeE : (0 : ℚ) <
      (nodes bits terms box derivativeSharp derivativeCorners).e.value.lower) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (evaluation bits terms box centerSharp derivativeSharp
        centerCorners derivativeCorners) := by
  have hcenterDomain :=
    LRUpperKHistoricalConcreteSoundness.openChartBoxCheck_centerBox hdomain
  refine
    { centerValue := ?_
      derivS := ?_
      derivK := ?_
      derivH := ?_ }
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hcenterDomain
      hcenterSharp hcenterCorners hcenterV hcenterE hcoordinate
    simpa [evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeCorners hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeCorners hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeCorners hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.2.2

/-- Midpoint data assembled from already materialized rounded node records.
Generated leaves use this small representation rather than repeating the
large exact evaluator result. -/
def evaluationOfNodes (bits : ℕ)
    (centerNodes derivativeNodes : Nodes) : MidpointCertificate :=
  let centerNode :=
    LRUpperKRoundedEvaluatorArithmetic.evaluateAD bits centerNodes
  let derivativeNode :=
    LRUpperKRoundedEvaluatorArithmetic.evaluateAD bits derivativeNodes
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

theorem centeredEvaluatorSoundness_of_nodes (bits terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    {centerNodes derivativeNodes : Nodes}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerSharp = true)
    (hcenterCorners : LRUpperKExplicitCornerPayload.check
      (centerBox box) centerCorners = true)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeCorners : LRUpperKExplicitCornerPayload.check
      box derivativeCorners = true)
    (hcenterNodes : centerNodes =
      nodes bits terms (centerBox box) centerSharp centerCorners)
    (hwholeNodes : derivativeNodes =
      nodes bits terms box derivativeSharp derivativeCorners)
    (hcenterV : (0 : ℚ) < centerNodes.v.value.lower)
    (hcenterE : (0 : ℚ) < centerNodes.e.value.lower)
    (hwholeV : (0 : ℚ) < derivativeNodes.v.value.lower)
    (hwholeE : (0 : ℚ) < derivativeNodes.e.value.lower) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (evaluationOfNodes bits centerNodes derivativeNodes) := by
  subst centerNodes
  subst derivativeNodes
  simpa [evaluationOfNodes, evaluation, evaluateAD] using
    centeredEvaluatorSoundness bits terms hdomain
      hcenterSharp hcenterCorners hwholeSharp hwholeCorners
      hcenterV hcenterE hwholeV hwholeE

theorem nonnegative_of_checked_nodes (bits terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerCorners derivativeCorners : CornerPayload}
    {centerNodes derivativeNodes : Nodes}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerSharp = true)
    (hcenterCorners : LRUpperKExplicitCornerPayload.check
      (centerBox box) centerCorners = true)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeCorners : LRUpperKExplicitCornerPayload.check
      box derivativeCorners = true)
    (hcenterNodes : centerNodes =
      nodes bits terms (centerBox box) centerSharp centerCorners)
    (hwholeNodes : derivativeNodes =
      nodes bits terms box derivativeSharp derivativeCorners)
    (hcenterV : (0 : ℚ) < centerNodes.v.value.lower)
    (hcenterE : (0 : ℚ) < centerNodes.e.value.lower)
    (hwholeV : (0 : ℚ) < derivativeNodes.v.value.lower)
    (hwholeE : (0 : ℚ) < derivativeNodes.e.value.lower)
    (hevaluation :
      (evaluationOfNodes bits centerNodes derivativeNodes).check box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hsound := centeredEvaluatorSoundness_of_nodes bits terms
    hdomain hcenterSharp hcenterCorners hwholeSharp hwholeCorners
    hcenterNodes hwholeNodes hcenterV hcenterE hwholeV hwholeE
  exact
    LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
      hdomain hsound hevaluation hcoordinate hrelevant

end LRUpperKRoundedExplicitCornerEvaluator
end CourtadeKumar
