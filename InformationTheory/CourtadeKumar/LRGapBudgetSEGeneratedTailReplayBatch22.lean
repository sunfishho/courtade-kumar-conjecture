import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk22 : Tree :=
  (.discard .xBelowHighShape)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk22_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).upper .chi (1/4)) = some chunk22 := by
  rfl'

theorem chunk22_check :
    chunk22.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).upper .chi (1/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).upper .chi (1/4)) chunk22 chunk22_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
