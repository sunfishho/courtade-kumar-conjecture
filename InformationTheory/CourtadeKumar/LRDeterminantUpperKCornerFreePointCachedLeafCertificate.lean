import InformationTheory.CourtadeKumar.LRDeterminantUpperKPointCachedCornerValues
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDirectCheckedTree

/-!
# Corner-free point-cached upper-`K` leaves

The point cache already supplies the four `A/C` value hulls, while the sharp
payload supplies their partial derivatives.  Consequently there is no need
to materialize the historical scalar-corner payload before overwriting its
four nodes.  This module constructs the twelve rounded evaluator nodes
literally and exposes a direct leaf checker whose computational path contains
no corner payload.
-/

namespace CourtadeKumar
namespace LRUpperKCornerFreePointEvaluator

open LRUpperKReplayCertificate
open LRUpperKHistoricalEvaluatorAssembly
open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKMidpointCoarsening
open LRUpperKDyadicOuterRounding

abbrev ScalarValues := LRUpperKPointCachedCornerValues.ScalarValues
abbrev SharpPayload := LRUpperKPointCachedCornerValues.SharpPayload
abbrev Nodes := LRUpperKExplicitEvaluatorNodes.Payload

/-- Materialize the twelve evaluator inputs directly.  In particular, the
four point-cached nodes are fields of this literal rather than updates to an
explicit-corner payload. -/
def materialize (terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : ScalarValues) : Nodes :=
  { bFlow := bFlowAD terms box sharp.base
    d1 := d1AD terms box sharp.base
    g0 := sharp.base.g0.evaluate terms (vAD box sharp.base)
    aY0 := LRUpperKCachedCornerValues.aY0AD terms box sharp values.assemble
    aE := LRUpperKCachedCornerValues.aEAD terms box sharp values.assemble
    cY0 := LRUpperKCachedCornerValues.cY0AD terms box sharp values.assemble
    cE := LRUpperKCachedCornerValues.cEAD terms box sharp values.assemble
    v := vAD box sharp.base
    kappa := kappaAD box sharp.base
    delta := deltaAD box sharp.base
    w := wAD terms box sharp.base
    e := eAD box }

def nodes (bits terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : ScalarValues) : Nodes :=
  LRUpperKRoundedEvaluatorArithmetic.outerNodes bits
    (materialize terms box sharp values)

def evaluateAD (bits terms : ℕ) (box : CertificateBox)
    (sharp : SharpPayload) (values : ScalarValues) : IntervalAD :=
  LRUpperKRoundedEvaluatorArithmetic.evaluateAD bits
    (nodes bits terms box sharp values)

/-- Semantic soundness of the literal point-cached node graph.  This reuses
the point endpoint-to-sharp-node bridge and the generic twelve-node rounded
arithmetic theorem. -/
theorem evaluateAD_sound (bits terms : ℕ)
    {box : CertificateBox} {sharp : SharpPayload}
    {values : ScalarValues}
    (hdomain : openChartBoxCheck box = true)
    (hsharp : LRUpperKHistoricalACAD.check terms box sharp = true)
    (hvalues : LRUpperKPointCachedCornerValues.EndpointSound box values)
    (hvRounded : (0 : ℚ) <
      (nodes bits terms box sharp values).v.value.lower)
    (heRounded : (0 : ℚ) <
      (nodes bits terms box sharp values).e.value.lower)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (evaluateAD bits terms box sharp values).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (targetChartDerivH coordinate) := by
  have hcommon :=
    LRUpperKHistoricalCommonComponents.commonComponentsAt_of_checked terms
      hsharp hcoordinate
  have hsharpNodes :=
    LRUpperKPointCachedCornerValues.sharpNodeEnclosures_of_checked terms
      hdomain hsharp hvalues hcoordinate
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
      (nodes bits terms box sharp values).bFlow
        (LRUpperKHistoricalCommonComponents.bFlowJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.bFlow
  have hd1 : Encloses
      (nodes bits terms box sharp values).d1
        (LRUpperKHistoricalCommonComponents.d1Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.d1
  have hg0 : Encloses
      (nodes bits terms box sharp values).g0
        (LRUpperKHistoricalCommonComponents.g0Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.g0
  have haY0 : Encloses
      (nodes bits terms box sharp values).aY0
        (LRUpperKHistoricalSharpNodeSoundness.aY0Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.aY0
  have haE : Encloses
      (nodes bits terms box sharp values).aE
        (LRUpperKHistoricalSharpNodeSoundness.aEJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.aE
  have hcY0 : Encloses
      (nodes bits terms box sharp values).cY0
        (LRUpperKHistoricalSharpNodeSoundness.cY0Jet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.cY0
  have hcE : Encloses
      (nodes bits terms box sharp values).cE
        (LRUpperKHistoricalSharpNodeSoundness.cEJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hsharpNodes.cE
  have hv : Encloses
      (nodes bits terms box sharp values).v
        (LRUpperKHistoricalCommonComponents.vJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.v
  have hkappa : Encloses
      (nodes bits terms box sharp values).kappa
        (LRUpperKHistoricalCommonComponents.kappaJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.kappa
  have hdelta : Encloses
      (nodes bits terms box sharp values).delta
        (LRUpperKHistoricalCommonComponents.deltaJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.delta
  have hw : Encloses
      (nodes bits terms box sharp values).w
        (LRUpperKHistoricalCommonComponents.wJet coordinate) := by
    simpa [nodes, materialize,
      LRUpperKRoundedEvaluatorArithmetic.outerNodes] using
      encloses_of_covers (outerIntervalAD_covers bits _) hcommon.w
  have he : Encloses
      (nodes bits terms box sharp values).e
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
  exact contains_upperKTarget_of_encloses hencloses hjet

def evaluation (bits terms : ℕ) (box : CertificateBox)
    (centerSharp derivativeSharp : SharpPayload)
    (centerValues derivativeValues : ScalarValues) : MidpointCertificate :=
  let centerNode := evaluateAD bits terms (centerBox box)
    centerSharp centerValues
  let derivativeNode := evaluateAD bits terms box
    derivativeSharp derivativeValues
  { value := centerNode.value
    derivS := derivativeNode.derivS
    derivK := derivativeNode.derivK
    derivChi := derivativeNode.derivChi }

theorem centeredEvaluatorSoundness (bits terms : ℕ)
    {box : CertificateBox}
    {centerSharp derivativeSharp : SharpPayload}
    {centerValues derivativeValues : ScalarValues}
    (hdomain : openChartBoxCheck box = true)
    (hcenterSharp : LRUpperKHistoricalACAD.check terms
      (centerBox box) centerSharp = true)
    (hcenterValues : LRUpperKPointCachedCornerValues.EndpointSound
      (centerBox box) centerValues)
    (hwholeSharp : LRUpperKHistoricalACAD.check terms box
      derivativeSharp = true)
    (hwholeValues : LRUpperKPointCachedCornerValues.EndpointSound
      box derivativeValues)
    (hcenterV : (0 : ℚ) <
      (nodes bits terms (centerBox box)
        centerSharp centerValues).v.value.lower)
    (hcenterE : (0 : ℚ) <
      (nodes bits terms (centerBox box)
        centerSharp centerValues).e.value.lower)
    (hwholeV : (0 : ℚ) <
      (nodes bits terms box derivativeSharp
        derivativeValues).v.value.lower)
    (hwholeE : (0 : ℚ) <
      (nodes bits terms box derivativeSharp
        derivativeValues).e.value.lower) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (evaluation bits terms box centerSharp derivativeSharp
        centerValues derivativeValues) := by
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
    simpa [evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound bits terms hdomain
      hwholeSharp hwholeValues hwholeV hwholeE hcoordinate
    simpa [evaluation] using hsound.2.2.2

end LRUpperKCornerFreePointEvaluator

namespace LRUpperKDirectCornerFreePointCachedLeafCertificate

open LRUpperKHistoricalThreeCoordinateBase

abbrev ScalarValues := LRUpperKCornerFreePointEvaluator.ScalarValues
abbrev EndpointSound := LRUpperKPointCachedCornerValues.EndpointSound

def centerSharp (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKHistoricalACAD.Payload :=
  LRUpperKHistoricalConcreteEvaluator.autoPayload sqrtFuel logFuel
    (centerBox box)

def wholeSharp (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKHistoricalACAD.Payload :=
  LRUpperKHistoricalConcreteEvaluator.autoPayload sqrtFuel logFuel box

def centerNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : ScalarValues) :
    LRUpperKExplicitEvaluatorNodes.Payload :=
  LRUpperKCornerFreePointEvaluator.nodes bits terms (centerBox box)
    (centerSharp sqrtFuel logFuel box) values

def wholeNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : ScalarValues) :
    LRUpperKExplicitEvaluatorNodes.Payload :=
  LRUpperKCornerFreePointEvaluator.nodes bits terms box
    (wholeSharp sqrtFuel logFuel box) values

def evaluation (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (centerValues wholeValues : ScalarValues) : MidpointCertificate :=
  LRUpperKCornerFreePointEvaluator.evaluation bits terms box
    (centerSharp sqrtFuel logFuel box)
    (wholeSharp sqrtFuel logFuel box)
    centerValues wholeValues

def analyticCheck (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  (LRUpperKReplayCertificate.openChartBoxCheck box &&
    LRUpperKHistoricalConcreteEvaluator.autoPayloadSucceeds
      terms sqrtFuel logFuel (centerBox box)) &&
  LRUpperKHistoricalConcreteEvaluator.autoPayloadSucceeds
    terms sqrtFuel logFuel box

def nodeCheck (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (centerValues wholeValues : ScalarValues) : Bool :=
  let cNodes := centerNodes bits terms sqrtFuel logFuel box centerValues
  let wNodes := wholeNodes bits terms sqrtFuel logFuel box wholeValues
  (decide ((0 : ℚ) < cNodes.v.value.lower) &&
    decide ((0 : ℚ) < cNodes.e.value.lower)) &&
  (decide ((0 : ℚ) < wNodes.v.value.lower) &&
    decide ((0 : ℚ) < wNodes.e.value.lower))

def evaluationCheck (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (centerValues wholeValues : ScalarValues) : Bool :=
  (evaluation bits terms sqrtFuel logFuel box
    centerValues wholeValues).check box

def check (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (centerValues wholeValues : ScalarValues) : Bool :=
  (analyticCheck terms sqrtFuel logFuel box &&
    nodeCheck bits terms sqrtFuel logFuel box centerValues wholeValues) &&
  evaluationCheck bits terms sqrtFuel logFuel box centerValues wholeValues

theorem nonnegative_of_factored_checks
    (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    {centerValues wholeValues : ScalarValues}
    (hanalytic : analyticCheck terms sqrtFuel logFuel box = true)
    (hcenterValues : EndpointSound (centerBox box) centerValues)
    (hwholeValues : EndpointSound box wholeValues)
    (hnodes : nodeCheck bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    (hevaluation : evaluationCheck bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : LRUpperKReplayCertificate.CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  simp only [analyticCheck, Bool.and_eq_true] at hanalytic
  simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hnodes
  have hcenterSharp : LRUpperKHistoricalACAD.check terms (centerBox box)
      (centerSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel (centerBox box) hanalytic.1.2
  have hwholeSharp : LRUpperKHistoricalACAD.check terms box
      (wholeSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel box hanalytic.2
  have hsound :=
    LRUpperKCornerFreePointEvaluator.centeredEvaluatorSoundness
      bits terms hanalytic.1.1 hcenterSharp hcenterValues
      hwholeSharp hwholeValues
      hnodes.1.1 hnodes.1.2 hnodes.2.1 hnodes.2.2
  exact
    LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
      hanalytic.1.1 hsound hevaluation hcoordinate hrelevant

theorem nonnegative_of_check
    (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    {centerValues wholeValues : ScalarValues}
    (hcheck : check bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    (hcenterValues : EndpointSound (centerBox box) centerValues)
    (hwholeValues : EndpointSound box wholeValues)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : LRUpperKReplayCertificate.CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  simp only [check, Bool.and_eq_true] at hcheck
  exact nonnegative_of_factored_checks bits terms sqrtFuel logFuel
    hcheck.1.1 hcenterValues hwholeValues hcheck.1.2 hcheck.2
    hcoordinate hrelevant

def checkedTreeOfFactoredChecks
    (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    {centerValues wholeValues : ScalarValues}
    (hanalytic : analyticCheck terms sqrtFuel logFuel box = true)
    (hcenterValues : EndpointSound (centerBox box) centerValues)
    (hwholeValues : EndpointSound box wholeValues)
    (hnodes : nodeCheck bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    (hevaluation : evaluationCheck bits terms sqrtFuel logFuel box
      centerValues wholeValues = true) :
    LRUpperKDirectCheckedTree.CheckedTree box :=
  LRUpperKDirectCheckedTree.CheckedTree.of_nonnegative (by
    intro coordinate hcoordinate hrelevant
    exact nonnegative_of_factored_checks bits terms sqrtFuel logFuel
      hanalytic hcenterValues hwholeValues hnodes hevaluation
      hcoordinate hrelevant)

def checkedTreeOfCheck
    (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    {centerValues wholeValues : ScalarValues}
    (hcheck : check bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    (hcenterValues : EndpointSound (centerBox box) centerValues)
    (hwholeValues : EndpointSound box wholeValues) :
    LRUpperKDirectCheckedTree.CheckedTree box :=
  LRUpperKDirectCheckedTree.CheckedTree.of_nonnegative (by
    intro coordinate hcoordinate hrelevant
    exact nonnegative_of_check bits terms sqrtFuel logFuel
      hcheck hcenterValues hwholeValues hcoordinate hrelevant)

end LRUpperKDirectCornerFreePointCachedLeafCertificate
end CourtadeKumar
