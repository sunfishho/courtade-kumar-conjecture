import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk23 : Tree :=
  (.split .k (3/4) (.discard .xBelowHighShape) (.discard .xBelowHighShape))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk23_generated_eq :
    buildEndpointTree 2 8 6 16
      (((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).upper .chi (1/2)) = some chunk23 := by
  rfl'

theorem chunk23_check :
    chunk23.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).upper .chi (1/2)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 16 (((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).upper .chi (1/2)) chunk23 chunk23_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
