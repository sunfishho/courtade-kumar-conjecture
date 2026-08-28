import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box3 : Box :=
  ((((root.lower .s (1 / 20)).lower .s (1 / 40)).upper .chi (1 / 2)).upper .chi (3 / 4))

def chunk3 : Tree :=
  match buildTree 3 10 8 8 box3 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk3_generated_eq :
    buildTree 3 10 8 8 box3 = some chunk3 := by
  rfl'

theorem chunk3_check : chunk3.check 3 10 8 box3 = true :=
  buildTree_check_of_eq 3 10 8 8 box3 chunk3 chunk3_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
