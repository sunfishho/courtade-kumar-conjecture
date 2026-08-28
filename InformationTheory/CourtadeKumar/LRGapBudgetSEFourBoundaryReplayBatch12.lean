import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch12Part0
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch12Part1
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch12Part2
import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplayBatch12Part3

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box12 : Box :=
  ((((root.upper .s (1 / 20)).upper .s (3 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4))

def chunk12 : Tree :=
  .split .s (7 / 80)
    (.split .chi (1 / 8) chunk120 chunk121)
    (.split .chi (1 / 8) chunk122 chunk123)

theorem chunk12_check : chunk12.check 3 10 8 box12 = true := by
  rw [chunk12]
  refine (Tree.check_split_iff 3 10 8 box12 .s (7 / 80) _ _).2 ⟨?_, ?_⟩
  · refine (Tree.check_split_iff 3 10 8 (box12.lower .s (7 / 80))
      .chi (1 / 8) chunk120 chunk121).2 ⟨?_, ?_⟩
    · simpa only [box12, box120] using chunk120_check
    · simpa only [box12, box121] using chunk121_check
  · refine (Tree.check_split_iff 3 10 8 (box12.upper .s (7 / 80))
      .chi (1 / 8) chunk122 chunk123).2 ⟨?_, ?_⟩
    · simpa only [box12, box122] using chunk122_check
    · simpa only [box12, box123] using chunk123_check

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
