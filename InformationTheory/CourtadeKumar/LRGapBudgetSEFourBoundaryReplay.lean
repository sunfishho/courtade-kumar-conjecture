import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch0
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch1
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch2
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch3
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch4
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch5
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch6
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch7
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch8
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch9
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch10
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch11
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch12
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch13
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch14
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch15

/-!
# Kernel replay of the complete `e = 4s` boundary

The root is partitioned into a `4 × 4` rational grid.  Each grid box imports
an independently kernel-reduced generated subtree; this file performs only
the structural reassembly.
-/

open Set

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def row (c0 c1 c2 c3 : Tree) : Tree :=
  .split .chi (1 / 2)
    (.split .chi (1 / 4) c0 c1)
    (.split .chi (3 / 4) c2 c3)

theorem row_check (box : Box) (c0 c1 c2 c3 : Tree)
    (h0 : c0.check 3 10 8
      ((box.lower .chi (1 / 2)).lower .chi (1 / 4)) = true)
    (h1 : c1.check 3 10 8
      ((box.lower .chi (1 / 2)).upper .chi (1 / 4)) = true)
    (h2 : c2.check 3 10 8
      ((box.upper .chi (1 / 2)).lower .chi (3 / 4)) = true)
    (h3 : c3.check 3 10 8
      ((box.upper .chi (1 / 2)).upper .chi (3 / 4)) = true) :
    (row c0 c1 c2 c3).check 3 10 8 box = true := by
  rw [row]
  refine (Tree.check_split_iff 3 10 8 box .chi (1 / 2) _ _).2 ⟨?_, ?_⟩
  · exact (Tree.check_split_iff 3 10 8 (box.lower .chi (1 / 2))
      .chi (1 / 4) c0 c1).2 ⟨h0, h1⟩
  · exact (Tree.check_split_iff 3 10 8 (box.upper .chi (1 / 2))
      .chi (3 / 4) c2 c3).2 ⟨h2, h3⟩

def band0 : Box := (root.lower .s (1 / 20)).lower .s (1 / 40)
def band1 : Box := (root.lower .s (1 / 20)).upper .s (1 / 40)
def band2 : Box := (root.upper .s (1 / 20)).lower .s (3 / 40)
def band3 : Box := (root.upper .s (1 / 20)).upper .s (3 / 40)

def row0 : Tree := row chunk0 chunk1 chunk2 chunk3
def row1 : Tree := row chunk4 chunk5 chunk6 chunk7
def row2 : Tree := row chunk8 chunk9 chunk10 chunk11
def row3 : Tree := row chunk12 chunk13 chunk14 chunk15

theorem row0_check : row0.check 3 10 8 band0 = true := by
  apply row_check
  · simpa only [band0, box0] using chunk0_check
  · simpa only [band0, box1] using chunk1_check
  · simpa only [band0, box2] using chunk2_check
  · simpa only [band0, box3] using chunk3_check

theorem row1_check : row1.check 3 10 8 band1 = true := by
  apply row_check
  · simpa only [band1, box4] using chunk4_check
  · simpa only [band1, box5] using chunk5_check
  · simpa only [band1, box6] using chunk6_check
  · simpa only [band1, box7] using chunk7_check

theorem row2_check : row2.check 3 10 8 band2 = true := by
  apply row_check
  · simpa only [band2, box8] using chunk8_check
  · simpa only [band2, box9] using chunk9_check
  · simpa only [band2, box10] using chunk10_check
  · simpa only [band2, box11] using chunk11_check

theorem row3_check : row3.check 3 10 8 band3 = true := by
  apply row_check
  · simpa only [band3, box12] using chunk12_check
  · simpa only [band3, box13] using chunk13_check
  · simpa only [band3, box14] using chunk14_check
  · simpa only [band3, box15] using chunk15_check

def tree : Tree :=
  .split .s (1 / 20)
    (.split .s (1 / 40) row0 row1)
    (.split .s (3 / 40) row2 row3)

theorem check_eq_true : tree.check 3 10 8 root = true := by
  rw [tree]
  refine (Tree.check_split_iff 3 10 8 root .s (1 / 20) _ _).2 ⟨?_, ?_⟩
  · exact (Tree.check_split_iff 3 10 8 (root.lower .s (1 / 20))
      .s (1 / 40) row0 row1).2
        ⟨by simpa only [band0] using row0_check,
          by simpa only [band1] using row1_check⟩
  · exact (Tree.check_split_iff 3 10 8 (root.upper .s (1 / 20))
      .s (3 / 40) row2 row3).2
        ⟨by simpa only [band2] using row2_check,
          by simpa only [band3] using row3_check⟩

/-- Fully replayed nonnegativity on the physical `k=4` boundary. -/
theorem gap_nonnegative
    {s chi : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 10 : ℝ))
    (hchi : chi ∈ Icc (0 : ℝ) 1)
    (hrelevant : LRGapBudgetSEFourBoundary.Relevant s chi) :
    0 ≤ lrGapBudgetSEChi s (4 * s) chi := by
  exact Tree.sound 3 10 8 check_eq_true s chi
    (root_contains hs hchi) hrelevant

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
