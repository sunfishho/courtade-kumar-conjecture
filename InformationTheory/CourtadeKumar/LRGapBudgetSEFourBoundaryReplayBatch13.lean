import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box13 : Box :=
  ((((root.upper .s (1 / 20)).upper .s (3 / 40)).lower .chi (1 / 2)).upper .chi (1 / 4))

def chunk13 : Tree :=
  match buildTree 3 10 8 8 box13 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk13_generated_eq :
    buildTree 3 10 8 8 box13 = some chunk13 := by
  rfl'

theorem chunk13_check : chunk13.check 3 10 8 box13 = true :=
  buildTree_check_of_eq 3 10 8 8 box13 chunk13 chunk13_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
