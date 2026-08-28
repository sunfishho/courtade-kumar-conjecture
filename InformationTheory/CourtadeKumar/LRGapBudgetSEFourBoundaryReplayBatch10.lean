import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box10 : Box :=
  ((((root.upper .s (1 / 20)).lower .s (3 / 40)).upper .chi (1 / 2)).lower .chi (3 / 4))

def chunk10 : Tree :=
  match buildTree 3 10 8 8 box10 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk10_generated_eq :
    buildTree 3 10 8 8 box10 = some chunk10 := by
  rfl'

theorem chunk10_check : chunk10.check 3 10 8 box10 = true :=
  buildTree_check_of_eq 3 10 8 8 box10 chunk10 chunk10_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
