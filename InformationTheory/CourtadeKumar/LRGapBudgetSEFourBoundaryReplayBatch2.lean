import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box2 : Box :=
  ((((root.lower .s (1 / 20)).lower .s (1 / 40)).upper .chi (1 / 2)).lower .chi (3 / 4))

def chunk2 : Tree :=
  match buildTree 3 10 8 8 box2 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk2_generated_eq :
    buildTree 3 10 8 8 box2 = some chunk2 := by
  rfl'

theorem chunk2_check : chunk2.check 3 10 8 box2 = true :=
  buildTree_check_of_eq 3 10 8 8 box2 chunk2 chunk2_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
