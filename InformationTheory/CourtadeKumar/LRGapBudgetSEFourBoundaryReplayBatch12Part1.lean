import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box121 : Box :=
  ((((((root.upper .s (1 / 20)).upper .s (3 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4)).lower .s (7 / 80)).upper .chi (1 / 8))

def chunk121 : Tree :=
  match buildTree 3 10 8 6 box121 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk121_generated_eq :
    buildTree 3 10 8 6 box121 = some chunk121 := by
  rfl'

theorem chunk121_check : chunk121.check 3 10 8 box121 = true :=
  buildTree_check_of_eq 3 10 8 6 box121 chunk121 chunk121_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
