import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box1 : Box :=
  ((((root.lower .s (1 / 20)).lower .s (1 / 40)).lower .chi (1 / 2)).upper .chi (1 / 4))

def chunk1 : Tree :=
  match buildTree 3 10 8 8 box1 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk1_generated_eq :
    buildTree 3 10 8 8 box1 = some chunk1 := by
  rfl'

theorem chunk1_check : chunk1.check 3 10 8 box1 = true :=
  buildTree_check_of_eq 3 10 8 8 box1 chunk1 chunk1_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
