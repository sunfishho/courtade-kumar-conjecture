import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box123 : Box :=
  ((((((root.upper .s (1 / 20)).upper .s (3 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4)).upper .s (7 / 80)).upper .chi (1 / 8))

def chunk123 : Tree :=
  match buildTree 3 10 8 6 box123 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk123_generated_eq :
    buildTree 3 10 8 6 box123 = some chunk123 := by
  rfl'

theorem chunk123_check : chunk123.check 3 10 8 box123 = true :=
  buildTree_check_of_eq 3 10 8 6 box123 chunk123 chunk123_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
