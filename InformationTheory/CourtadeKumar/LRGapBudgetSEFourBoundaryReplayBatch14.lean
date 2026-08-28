import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box14 : Box :=
  ((((root.upper .s (1 / 20)).upper .s (3 / 40)).upper .chi (1 / 2)).lower .chi (3 / 4))

def chunk14 : Tree :=
  match buildTree 3 10 8 8 box14 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk14_generated_eq :
    buildTree 3 10 8 8 box14 = some chunk14 := by
  rfl'

theorem chunk14_check : chunk14.check 3 10 8 box14 = true :=
  buildTree_check_of_eq 3 10 8 8 box14 chunk14 chunk14_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
