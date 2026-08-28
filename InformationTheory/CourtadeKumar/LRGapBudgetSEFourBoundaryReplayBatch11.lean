import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box11 : Box :=
  ((((root.upper .s (1 / 20)).lower .s (3 / 40)).upper .chi (1 / 2)).upper .chi (3 / 4))

def chunk11 : Tree :=
  match buildTree 3 10 8 8 box11 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk11_generated_eq :
    buildTree 3 10 8 8 box11 = some chunk11 := by
  rfl'

theorem chunk11_check : chunk11.check 3 10 8 box11 = true :=
  buildTree_check_of_eq 3 10 8 8 box11 chunk11 chunk11_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
