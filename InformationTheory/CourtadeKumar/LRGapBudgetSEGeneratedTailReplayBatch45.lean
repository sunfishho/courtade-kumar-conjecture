import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk45 : Tree :=
  (.discard .vBelowThird)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk45_generated_eq :
    buildEndpointTree 2 8 6 9
      ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (17/800)).upper .k (15/16)) = some chunk45 := by
  rfl'

theorem chunk45_check :
    chunk45.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (17/800)).upper .k (15/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 9 ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (17/800)).upper .k (15/16)) chunk45 chunk45_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
