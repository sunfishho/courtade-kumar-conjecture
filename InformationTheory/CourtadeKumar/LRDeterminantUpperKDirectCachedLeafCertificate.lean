import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedCornerValues
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDirectLeafCertificate

/-!
# Direct leaves with reusable cached corner values

The analytic constructors remain deterministic.  Only the four center and
four whole `A/C` value hulls are supplied by authenticated cache modules.
-/

namespace CourtadeKumar
namespace LRUpperKDirectCachedLeafCertificate

open LRUpperKHistoricalThreeCoordinateBase

abbrev Values := LRUpperKCachedCornerValues.Values

def centerNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : Values) :
    LRUpperKExplicitEvaluatorNodes.Payload :=
  LRUpperKCachedCornerValues.nodes bits terms (centerBox box)
    (LRUpperKDirectLeafCertificate.centerSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box)
    values

def wholeNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (values : Values) :
    LRUpperKExplicitEvaluatorNodes.Payload :=
  LRUpperKCachedCornerValues.nodes bits terms box
    (LRUpperKDirectLeafCertificate.wholeSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box)
    values

def evaluation (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (centerValues wholeValues : Values) :
    MidpointCertificate :=
  LRUpperKCachedCornerValues.evaluation bits terms box
    (LRUpperKDirectLeafCertificate.centerSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.wholeSharp sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box)
    (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box)
    centerValues wholeValues

def nodeCheck (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (centerValues wholeValues : Values) : Bool :=
  let cNodes := centerNodes bits terms sqrtFuel logFuel box centerValues
  let wNodes := wholeNodes bits terms sqrtFuel logFuel box wholeValues
  (decide ((0 : ℚ) < cNodes.v.value.lower) &&
    decide ((0 : ℚ) < cNodes.e.value.lower)) &&
  (decide ((0 : ℚ) < wNodes.v.value.lower) &&
    decide ((0 : ℚ) < wNodes.e.value.lower))

def evaluationCheck (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (centerValues wholeValues : Values) : Bool :=
  (evaluation bits terms sqrtFuel logFuel box centerValues wholeValues).check box

theorem nonnegative_of_factored_checks (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox} {centerValues wholeValues : Values}
    (hanalytic : LRUpperKDirectLeafCertificate.analyticCheck
      terms sqrtFuel logFuel box = true)
    (hcenterValues : LRUpperKCachedCornerValues.CoversExact terms
      (centerBox box)
      (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box)
      centerValues)
    (hwholeValues : LRUpperKCachedCornerValues.CoversExact terms box
      (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box)
      wholeValues)
    (hnodes : nodeCheck bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    (hevaluation : evaluationCheck bits terms sqrtFuel logFuel box
      centerValues wholeValues = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : LRUpperKReplayCertificate.CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  simp only [LRUpperKDirectLeafCertificate.analyticCheck,
    Bool.and_eq_true] at hanalytic
  simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hnodes
  have hcenterSharp : LRUpperKHistoricalACAD.check terms (centerBox box)
      (LRUpperKDirectLeafCertificate.centerSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel (centerBox box) hanalytic.1.1.2
  have hwholeSharp : LRUpperKHistoricalACAD.check terms box
      (LRUpperKDirectLeafCertificate.wholeSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel box hanalytic.1.2.1
  have hcenterCorners : LRUpperKExplicitCornerPayload.check (centerBox box)
      (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box) = true :=
    LRUpperKExplicitCornerPayload.auto_check_of_succeeds
      sqrtFuel logFuel (centerBox box) hanalytic.1.2.2
  have hwholeCorners : LRUpperKExplicitCornerPayload.check box
      (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box) = true :=
    LRUpperKExplicitCornerPayload.auto_check_of_succeeds
      sqrtFuel logFuel box hanalytic.2
  exact LRUpperKCachedCornerValues.nonnegative_of_checked bits terms
    hanalytic.1.1.1 hcenterSharp hcenterCorners hcenterValues
    hwholeSharp hwholeCorners hwholeValues
    hnodes.1.1 hnodes.1.2 hnodes.2.1 hnodes.2.2
    hevaluation hcoordinate hrelevant

def checkedTreeOfFactoredChecks (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox} {centerValues wholeValues : Values}
    (hanalytic : LRUpperKDirectLeafCertificate.analyticCheck
      terms sqrtFuel logFuel box = true)
    (hcenterValues : LRUpperKCachedCornerValues.CoversExact terms
      (centerBox box)
      (LRUpperKDirectLeafCertificate.centerCorners sqrtFuel logFuel box)
      centerValues)
    (hwholeValues : LRUpperKCachedCornerValues.CoversExact terms box
      (LRUpperKDirectLeafCertificate.wholeCorners sqrtFuel logFuel box)
      wholeValues)
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

end LRUpperKDirectCachedLeafCertificate
end CourtadeKumar
