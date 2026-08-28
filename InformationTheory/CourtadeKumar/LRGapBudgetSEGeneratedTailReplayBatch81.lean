import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk81 : Tree :=
  (.discard .xBelowHighShape)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk81_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).upper .chi (1/4)) = some chunk81 := by
  rfl'

theorem chunk81_check :
    chunk81.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).upper .chi (1/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).upper .chi (1/4)) chunk81 chunk81_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
