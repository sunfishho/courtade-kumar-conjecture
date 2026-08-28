import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box120 : Box :=
  ((((((root.upper .s (1 / 20)).upper .s (3 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4)).lower .s (7 / 80)).lower .chi (1 / 8))

def chunk120 : Tree :=
  match buildTree 3 10 8 6 box120 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk120_generated_eq :
    buildTree 3 10 8 6 box120 = some chunk120 := by
  rfl'

theorem chunk120_check : chunk120.check 3 10 8 box120 = true :=
  buildTree_check_of_eq 3 10 8 6 box120 chunk120 chunk120_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
