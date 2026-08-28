import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box122 : Box :=
  ((((((root.upper .s (1 / 20)).upper .s (3 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4)).upper .s (7 / 80)).lower .chi (1 / 8))

def chunk122 : Tree :=
  match buildTree 3 10 8 6 box122 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk122_generated_eq :
    buildTree 3 10 8 6 box122 = some chunk122 := by
  rfl'

theorem chunk122_check : chunk122.check 3 10 8 box122 = true :=
  buildTree_check_of_eq 3 10 8 6 box122 chunk122 chunk122_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
