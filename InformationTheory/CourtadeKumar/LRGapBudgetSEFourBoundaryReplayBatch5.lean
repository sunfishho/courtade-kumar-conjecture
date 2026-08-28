import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundary

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryReplay

open LRGapBudgetSEFourBoundary

def box5 : Box :=
  ((((root.lower .s (1 / 20)).upper .s (1 / 40)).lower .chi (1 / 2)).upper .chi (1 / 4))

def chunk5 : Tree :=
  match buildTree 3 10 8 8 box5 with
  | some tree => tree
  | none => .accept

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk5_generated_eq :
    buildTree 3 10 8 8 box5 = some chunk5 := by
  rfl'

theorem chunk5_check : chunk5.check 3 10 8 box5 = true :=
  buildTree_check_of_eq 3 10 8 8 box5 chunk5 chunk5_generated_eq

end LRGapBudgetSEFourBoundaryReplay
end CourtadeKumar
