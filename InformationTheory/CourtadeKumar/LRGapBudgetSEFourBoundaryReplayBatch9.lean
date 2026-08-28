import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box9 : Box :=
  ((((root.upper .s (1 / 20)).lower .s (3 / 40)).lower .chi (1 / 2)).upper .chi (1 / 4))

def chunk9 : Tree :=
  match buildTree 3 10 8 8 box9 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk9_generated_eq :
    buildTree 3 10 8 8 box9 = some chunk9 := by
  rfl'

theorem chunk9_check : chunk9.check 3 10 8 box9 = true :=
  buildTree_check_of_eq 3 10 8 8 box9 chunk9 chunk9_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
