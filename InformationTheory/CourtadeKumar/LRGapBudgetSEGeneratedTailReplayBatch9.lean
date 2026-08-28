import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk9 : Tree :=
  (.split .chi (1/4) (.split .k (5/8) (.split .chi (1/8) (.accept .endpointRetainedQ) (.accept .endpoint)) (.split .chi (1/8) (.split .k (11/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (11/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .k (5/8) (.split .chi (3/8) (.accept .endpoint) (.accept .endpoint)) (.split .chi (3/8) (.split .k (11/16) (.accept .endpoint) (.discard .xBelowHighShape)) (.discard .xBelowHighShape))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk9_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).upper .s (1/10000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) = some chunk9 := by
  rfl'

theorem chunk9_check :
    chunk9.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).upper .s (1/10000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).upper .s (1/10000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) chunk9 chunk9_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
