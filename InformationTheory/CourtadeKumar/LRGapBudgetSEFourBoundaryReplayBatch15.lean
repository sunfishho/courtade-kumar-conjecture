import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box15 : Box :=
  ((((root.upper .s (1 / 20)).upper .s (3 / 40)).upper .chi (1 / 2)).upper .chi (3 / 4))

def chunk15 : Tree :=
  match buildTree 3 10 8 8 box15 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk15_generated_eq :
    buildTree 3 10 8 8 box15 = some chunk15 := by
  rfl'

theorem chunk15_check : chunk15.check 3 10 8 box15 = true :=
  buildTree_check_of_eq 3 10 8 8 box15 chunk15 chunk15_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
