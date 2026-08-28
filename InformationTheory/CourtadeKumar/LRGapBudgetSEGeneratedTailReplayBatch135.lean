import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk135 : Tree :=
  (.discard .xBelowHighShape)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk135_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).upper .chi (1/4)) = some chunk135 := by
  rfl'

theorem chunk135_check :
    chunk135.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).upper .chi (1/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).upper .chi (1/4)) chunk135 chunk135_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
