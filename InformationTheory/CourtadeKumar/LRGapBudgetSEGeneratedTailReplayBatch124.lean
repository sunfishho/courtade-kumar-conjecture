import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk124 : Tree :=
  (.split .k (29/32) (.split .chi (3/32) (.split .s (293/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (5/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (5/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .s (293/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (7/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (7/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk124_generated_eq :
    buildEndpointTree 2 8 6 7
      ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (71/800)).lower .k (15/16)).upper .chi (1/16)).lower .s (151/1600)) = some chunk124 := by
  rfl'

theorem chunk124_check :
    chunk124.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (71/800)).lower .k (15/16)).upper .chi (1/16)).lower .s (151/1600)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 7 ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (71/800)).lower .k (15/16)).upper .chi (1/16)).lower .s (151/1600)) chunk124 chunk124_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
