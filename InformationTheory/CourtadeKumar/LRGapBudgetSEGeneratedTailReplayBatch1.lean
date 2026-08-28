import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk1 : Tree :=
  (.split .chi (1/4) (.split .k (5/8) (.split .chi (1/8) (.accept .endpoint) (.accept .endpoint)) (.split .chi (1/8) (.split .k (11/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (11/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .k (5/8) (.accept .endpoint) (.split .chi (3/8) (.split .k (11/16) (.accept .endpoint) (.accept .endpointRetainedQ)) (.discard .xBelowHighShape))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk1_generated_eq :
    buildEndpointTree 2 8 6 13
      ((((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) = some chunk1 := by
  rfl'

theorem chunk1_check :
    chunk1.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 13 ((((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) chunk1 chunk1_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
