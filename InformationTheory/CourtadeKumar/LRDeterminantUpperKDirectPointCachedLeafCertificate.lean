import InformationTheory.CourtadeKumar.LRDeterminantUpperKPointCachedCornerValues
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDirectLeafCertificate

/-!
# Direct upper-`K` leaves backed by shared point certificates

The leaf imports eight scalar endpoint enclosures justified by shared
`Q/Q'` point caches.  It therefore checks only the sharp derivative payloads;
the redundant automatic `A/C` corner payload checks are absent.
-/

namespace CourtadeKumar
namespace LRUpperKDirectPointCachedLeafCertificate

open LRUpperKHistoricalThreeCoordinateBase

abbrev ScalarValues := LRUpperKCachedCornerValues.ScalarValues
abbrev EndpointSound := LRUpperKPointCachedCornerValues.EndpointSound

def centerNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : ScalarValues) :
    LRUpperKExplicitEvaluatorNodes.Payload :=
  LRUpperKCachedCornerValues.nodes bits terms (centerBox box)
    (LRUpperKDirectLeafCertificate.centerSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box)
    values.assemble

def wholeNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : ScalarValues) :
    LRUpperKExplicitEvaluatorNodes.Payload :=
  LRUpperKCachedCornerValues.nodes bits terms box
    (LRUpperKDirectLeafCertificate.wholeSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box)
    values.assemble

def evaluation (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (centerValues wholeValues : ScalarValues) : MidpointCertificate :=
  LRUpperKPointCachedCornerValues.evaluation bits terms box
    (LRUpperKDirectLeafCertificate.centerSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.wholeSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box)
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
      (LRUpperKDirectLeafCertificate.centerSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel (centerBox box) hanalytic.1.2
  have hwholeSharp : LRUpperKHistoricalACAD.check terms box
      (LRUpperKDirectLeafCertificate.wholeSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel box hanalytic.2
  have hsound := LRUpperKPointCachedCornerValues.centeredEvaluatorSoundness
    bits terms hanalytic.1.1 hcenterSharp hcenterValues
    hwholeSharp hwholeValues
    hnodes.1.1 hnodes.1.2 hnodes.2.1 hnodes.2.2
  exact
    LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
      hanalytic.1.1 hsound hevaluation hcoordinate hrelevant

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

end LRUpperKDirectPointCachedLeafCertificate
end CourtadeKumar
