import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box4 : Box :=
  ((((root.lower .s (1 / 20)).upper .s (1 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4))

def chunk4 : Tree :=
  match buildTree 3 10 8 8 box4 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk4_generated_eq :
    buildTree 3 10 8 8 box4 = some chunk4 := by
  rfl'

theorem chunk4_check : chunk4.check 3 10 8 box4 = true :=
  buildTree_check_of_eq 3 10 8 8 box4 chunk4 chunk4_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
