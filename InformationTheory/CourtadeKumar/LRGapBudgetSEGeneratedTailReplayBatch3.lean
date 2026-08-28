import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk3 : Tree :=
  (.split .k (3/4) (.discard .xBelowHighShape) (.discard .xBelowHighShape))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk3_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).upper .k (1/2)).upper .chi (1/2)) = some chunk3 := by
  rfl'

theorem chunk3_check :
    chunk3.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).upper .k (1/2)).upper .chi (1/2)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).upper .k (1/2)).upper .chi (1/2)) chunk3 chunk3_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
