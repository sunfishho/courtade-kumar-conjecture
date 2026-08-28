import InformationTheory.CourtadeKumar.LRGapBudgetSEGeneratedTailTreeData

/-!
# Replayed certificate for the complete bounded gap-budget tail

The following finite tree was generated from exact rational arithmetic and
is stored explicitly in `LRGapBudgetSEGeneratedTailTreeData`.  This module
exposes the single aggregate Boolean replay obligation and connects it to
the derivative hypothesis needed by the analytic tail argument.  The replay
is deliberately kept separate so it can be partitioned into small
kernel-checkable chunks without using `native_decide`.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailCertificate

open LRGapBudgetSECombinedAutoTree

def terms : ℕ := 30
def sqrtFuel : ℕ := 48
def logFuel : ℕ := 56

abbrev tree : Tree := LRGapBudgetSEGeneratedTailTreeData.tree

def checkResult : Bool :=
    tree.check
      (LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck lrGapBudgetSETailRoot

theorem derivative_nonnegative
    (hcheck : checkResult = true)
    (point : CertificatePoint)
    (hpoint : lrGapBudgetSETailRoot.Contains point)
    (hrelevant : LRGapBudgetSETailRelevant point) :
    0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi :=
  lrGapBudgetSECombinedDerivativeSubdivision_sound
    terms sqrtFuel logFuel hcheck point hpoint hrelevant

/-- Fully replayed derivative conclusion in the original `(s,k,chi)`
coordinates throughout the noncompact high-shape tail `k ≥ 4`. -/
theorem gapBudgetDerivK_nonnegative
    (hcheck : checkResult = true)
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    0 ≤ lrCertificateGapBudgetDerivK point :=
  lrCertificateGapBudgetDerivK_nonnegative_of_combinedSETail
    terms sqrtFuel logFuel hcheck hinterior hphysical hs hk

end LRGapBudgetSEGeneratedTailCertificate
end CourtadeKumar
