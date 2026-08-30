import InformationTheory.CourtadeKumar.LRDeterminantUpperKAutoCornerCorrectness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDirectCheckedTree

/-!
# One-check direct upper-K leaf certificates

All deterministic payload, rounded-node, positivity, and midpoint checks are
collected in one shallow Boolean. Its soundness theorem produces a semantic
checked leaf suitable for proof-preserving structural joins.
-/

namespace CourtadeKumar
namespace LRUpperKDirectLeafCertificate

open LRUpperKHistoricalThreeCoordinateBase
open LRUpperKRoundedExplicitCornerEvaluator

def centerSharp (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKHistoricalACAD.Payload :=
  LRUpperKHistoricalConcreteEvaluator.autoPayload sqrtFuel logFuel
    (centerBox box)

def wholeSharp (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKHistoricalACAD.Payload :=
  LRUpperKHistoricalConcreteEvaluator.autoPayload sqrtFuel logFuel box

def centerCorners (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKExplicitCornerPayload.Payload :=
  LRUpperKExplicitCornerPayload.auto sqrtFuel logFuel (centerBox box)

def wholeCorners (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRUpperKExplicitCornerPayload.Payload :=
  LRUpperKExplicitCornerPayload.auto sqrtFuel logFuel box

def centerNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : LRUpperKExplicitEvaluatorNodes.Payload :=
  nodes bits terms (centerBox box)
    (centerSharp sqrtFuel logFuel box)
    (centerCorners sqrtFuel logFuel box)

def wholeNodes (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : LRUpperKExplicitEvaluatorNodes.Payload :=
  nodes bits terms box
    (wholeSharp sqrtFuel logFuel box)
    (wholeCorners sqrtFuel logFuel box)

def evaluation (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : MidpointCertificate :=
  evaluationOfNodes bits
    (centerNodes bits terms sqrtFuel logFuel box)
    (wholeNodes bits terms sqrtFuel logFuel box)

def check (bits terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  let cNodes := centerNodes bits terms sqrtFuel logFuel box
  let wNodes := wholeNodes bits terms sqrtFuel logFuel box
  (((LRUpperKReplayCertificate.openChartBoxCheck box &&
        LRUpperKHistoricalConcreteEvaluator.autoPayloadSucceeds
          terms sqrtFuel logFuel (centerBox box)) &&
      (LRUpperKHistoricalConcreteEvaluator.autoPayloadSucceeds
          terms sqrtFuel logFuel box &&
        LRUpperKExplicitCornerPayload.autoSucceeds
          sqrtFuel logFuel (centerBox box))) &&
    ((LRUpperKExplicitCornerPayload.autoSucceeds sqrtFuel logFuel box &&
        decide ((0 : ℚ) < cNodes.v.value.lower)) &&
      (decide ((0 : ℚ) < cNodes.e.value.lower) &&
        decide ((0 : ℚ) < wNodes.v.value.lower)))) &&
  (decide ((0 : ℚ) < wNodes.e.value.lower) &&
    (evaluation bits terms sqrtFuel logFuel box).check box)

theorem nonnegative_of_check (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    (hcheck : check bits terms sqrtFuel logFuel box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : LRUpperKReplayCertificate.CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hcenterSharp : LRUpperKHistoricalACAD.check terms (centerBox box)
      (centerSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel (centerBox box) hcheck.1.1.1.2
  have hwholeSharp : LRUpperKHistoricalACAD.check terms box
      (wholeSharp sqrtFuel logFuel box) = true :=
    LRUpperKHistoricalConcreteEvaluator.autoPayload_check_of_succeeds
      terms sqrtFuel logFuel box hcheck.1.1.2.1
  have hcenterCorners : LRUpperKExplicitCornerPayload.check (centerBox box)
      (centerCorners sqrtFuel logFuel box) = true :=
    LRUpperKExplicitCornerPayload.auto_check_of_succeeds
      sqrtFuel logFuel (centerBox box) hcheck.1.1.2.2
  have hwholeCorners : LRUpperKExplicitCornerPayload.check box
      (wholeCorners sqrtFuel logFuel box) = true :=
    LRUpperKExplicitCornerPayload.auto_check_of_succeeds
      sqrtFuel logFuel box hcheck.1.2.1.1
  exact nonnegative_of_checked_nodes bits terms
    hcheck.1.1.1.1 hcenterSharp hcenterCorners hwholeSharp hwholeCorners
    rfl rfl hcheck.1.2.1.2 hcheck.1.2.2.1 hcheck.1.2.2.2 hcheck.2.1
    hcheck.2.2 hcoordinate hrelevant

def checkedTreeOfCheck (bits terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    (hcheck : check bits terms sqrtFuel logFuel box = true) :
    LRUpperKDirectCheckedTree.CheckedTree box :=
  LRUpperKDirectCheckedTree.CheckedTree.of_nonnegative (by
    intro coordinate hcoordinate hrelevant
    exact nonnegative_of_check bits terms sqrtFuel logFuel hcheck
      hcoordinate hrelevant)

end LRUpperKDirectLeafCertificate
end CourtadeKumar
