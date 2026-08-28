import InformationTheory.CourtadeKumar.LRGapBudgetSEGeneratedTailReplay

/-!
# Replayed certificate for the complete bounded gap-budget tail

The finite tree is partitioned into independently replayed subtrees.  Each
subtree is definitionally identified with the output of the deterministic
endpoint generator using full-transparency kernel reduction, and the
structural generator theorem supplies its checked-leaf conclusion.  The
assembled result contains no `native_decide` or external proof oracle.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailCertificate

open LRGapBudgetSECombinedAutoTree

def terms : ℕ := 2
def sqrtFuel : ℕ := 8
def logFuel : ℕ := 6

abbrev tree : Tree := LRGapBudgetSEGeneratedTailReplay.tree

def checkResult : Bool :=
    tree.check
      (LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck lrGapBudgetSETailRoot

theorem checkResult_eq_true : checkResult = true := by
  simpa [checkResult, terms, sqrtFuel, logFuel] using
    LRGapBudgetSEGeneratedTailReplay.check_eq_true

theorem derivative_nonnegative
    (hcheck : checkResult = true)
    (point : CertificatePoint)
    (hpoint : lrGapBudgetSETailRoot.Contains point)
    (hrelevant : LRGapBudgetSETailRelevant point) :
    0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi :=
  lrGapBudgetSECombinedDerivativeSubdivision_sound
    terms sqrtFuel logFuel hcheck point hpoint hrelevant

theorem derivative_nonnegative_unconditional
    (point : CertificatePoint)
    (hpoint : lrGapBudgetSETailRoot.Contains point)
    (hrelevant : LRGapBudgetSETailRelevant point) :
    0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi :=
  derivative_nonnegative checkResult_eq_true point hpoint hrelevant

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

theorem gapBudgetDerivK_nonnegative_unconditional
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    0 ≤ lrCertificateGapBudgetDerivK point :=
  gapBudgetDerivK_nonnegative checkResult_eq_true hinterior hphysical hs hk

end LRGapBudgetSEGeneratedTailCertificate
end CourtadeKumar
