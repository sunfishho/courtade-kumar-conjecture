import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk21 : Tree :=
  (.discard .vBelowThird)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk21_generated_eq :
    buildEndpointTree 2 8 6 11
      ((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).upper .k (15/16)) = some chunk21 := by
  rfl'

theorem chunk21_check :
    chunk21.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).upper .k (15/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 11 ((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).upper .k (15/16)) chunk21 chunk21_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
