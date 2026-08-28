import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box6 : Box :=
  ((((root.lower .s (1 / 20)).upper .s (1 / 40)).upper .chi (1 / 2)).lower .chi (3 / 4))

def chunk6 : Tree :=
  match buildTree 3 10 8 8 box6 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk6_generated_eq :
    buildTree 3 10 8 8 box6 = some chunk6 := by
  rfl'

theorem chunk6_check : chunk6.check 3 10 8 box6 = true :=
  buildTree_check_of_eq 3 10 8 8 box6 chunk6 chunk6_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
