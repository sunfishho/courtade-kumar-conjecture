import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box7 : Box :=
  ((((root.lower .s (1 / 20)).upper .s (1 / 40)).upper .chi (1 / 2)).upper .chi (3 / 4))

def chunk7 : Tree :=
  match buildTree 3 10 8 8 box7 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk7_generated_eq :
    buildTree 3 10 8 8 box7 = some chunk7 := by
  rfl'

theorem chunk7_check : chunk7.check 3 10 8 box7 = true :=
  buildTree_check_of_eq 3 10 8 8 box7 chunk7 chunk7_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
