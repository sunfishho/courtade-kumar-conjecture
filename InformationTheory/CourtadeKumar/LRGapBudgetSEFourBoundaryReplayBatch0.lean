import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box0 : Box :=
  ((((root.lower .s (1 / 20)).lower .s (1 / 40)).lower .chi (1 / 2)).lower .chi (1 / 4))

def chunk0 : Tree :=
  match buildTree 3 10 8 8 box0 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk0_generated_eq :
    buildTree 3 10 8 8 box0 = some chunk0 := by
  rfl'

theorem chunk0_check : chunk0.check 3 10 8 box0 = true :=
  buildTree_check_of_eq 3 10 8 8 box0 chunk0 chunk0_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
