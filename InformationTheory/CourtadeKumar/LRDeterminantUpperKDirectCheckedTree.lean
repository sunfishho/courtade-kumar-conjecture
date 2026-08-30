import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalPackedCertificate

/-!
# Semantic checked trees for direct upper-K leaf proofs

Unlike the historical Boolean tree, leaves carry an already kernel-checked
target theorem. Structural joins therefore never replay leaf arithmetic.
-/

namespace CourtadeKumar
namespace LRUpperKDirectCheckedTree

open LRUpperKReplayCertificate

structure CheckedTree (root : CertificateBox) : Type where
  target_nonnegative :
    ∀ coordinate, root.Contains coordinate → CenteredRelevant coordinate →
      0 ≤ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate)

abbrev CheckedChunk := CheckedTree

namespace CheckedTree

def of_nonnegative {root : CertificateBox}
    (h : ∀ coordinate, root.Contains coordinate → CenteredRelevant coordinate →
      0 ≤ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate)) :
    CheckedTree root :=
  ⟨h⟩

def join {root : CertificateBox} (axis : CertificateAxis)
    (lower : CheckedTree
      (root.lower axis (LRUpperKHistoricalAutoTree.axisCut root axis)))
    (upper : CheckedTree
      (root.upper axis (LRUpperKHistoricalAutoTree.axisCut root axis))) :
    CheckedTree root :=
  ⟨by
    intro coordinate hcoordinate hrelevant
    rcases root.contains_lower_or_upper hcoordinate axis
        (LRUpperKHistoricalAutoTree.axisCut root axis) with hlower | hupper
    · exact lower.target_nonnegative coordinate hlower hrelevant
    · exact upper.target_nonnegative coordinate hupper hrelevant⟩

end CheckedTree

open LRUpperKHistoricalPackedCertificate

abbrev CheckedAtPath
    (ancestor : CertificateBox) (path : Path) : Type :=
  CheckedTree (follow ancestor path)

def joinAtPath {ancestor : CertificateBox}
    (path : Path) (axis : CertificateAxis)
    (lower : CheckedAtPath ancestor (path ++ [lowerStep axis]))
    (upper : CheckedAtPath ancestor (path ++ [upperStep axis])) :
    CheckedAtPath ancestor path :=
  CheckedTree.join axis
    (by simpa only [CheckedAtPath, follow_append_lower] using lower)
    (by simpa only [CheckedAtPath, follow_append_upper] using upper)

def checkedTreeOfEmptyPath {root : CertificateBox}
    (chunk : CheckedAtPath root []) : CheckedTree root := by
  simpa [CheckedAtPath, follow, LRUpperKHistoricalPackedCertificate.Auto.follow]
    using chunk

abbrev oneToTwoRoot := LRUpperKHistoricalAutoTree.oneToTwoRoot
abbrev twoToFourRoot := LRUpperKHistoricalAutoTree.twoToFourRoot

theorem upperKRegionCertificate_of_twoCheckedTrees
    (tree12 : CheckedTree oneToTwoRoot)
    (tree24 : CheckedTree twoToFourRoot) :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hchartRelevant : CenteredRelevant
      (lrDeterminantKChartEncode point) := by
    unfold CenteredRelevant
    rw [hdecoded]
    exact ⟨hinterior, hrelevant⟩
  have hroot :=
    lrDeterminantUpperKKChartRoot_contains_encode hinterior hregion
  rcases CertificateBox.contains_lower_or_upper hroot .k 2 with h12 | h24
  · have htarget := tree12.target_nonnegative
      (lrDeterminantKChartEncode point) h12 hchartRelevant
    rw [hdecoded] at htarget
    exact lrDeterminantAdmittedTarget_of_upperKReplayTarget hinterior htarget
  · have htarget := tree24.target_nonnegative
      (lrDeterminantKChartEncode point) h24 hchartRelevant
    rw [hdecoded] at htarget
    exact lrDeterminantAdmittedTarget_of_upperKReplayTarget hinterior htarget

end LRUpperKDirectCheckedTree
end CourtadeKumar
