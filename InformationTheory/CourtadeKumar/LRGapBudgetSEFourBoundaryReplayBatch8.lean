import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box8 : Box :=
  ((((root.upper .s (1 / 20)).lower .s (3 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4))

def chunk8 : Tree :=
  match buildTree 3 10 8 8 box8 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk8_generated_eq :
    buildTree 3 10 8 8 box8 = some chunk8 := by
  rfl'

theorem chunk8_check : chunk8.check 3 10 8 box8 = true :=
  buildTree_check_of_eq 3 10 8 8 box8 chunk8 chunk8_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
