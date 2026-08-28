import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk19 : Tree :=
  (.split .k (29/32) (.split .chi (5/32) (.split .s (31/4000) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (31/4000) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .chi (5/32) (.discard .vBelowThird) (.split .s (31/4000) (.split .k (59/64) (.split .chi (11/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.discard .vBelowThird)) (.split .k (59/64) (.split .chi (11/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.discard .vBelowThird)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk19_generated_eq :
    buildEndpointTree 2 8 6 9
      ((((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).lower .k (15/16)).lower .chi (3/16)).upper .s (11/2000)) = some chunk19 := by
  rfl'

theorem chunk19_check :
    chunk19.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).lower .k (15/16)).lower .chi (3/16)).upper .s (11/2000)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 9 ((((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).lower .k (15/16)).lower .chi (3/16)).upper .s (11/2000)) chunk19 chunk19_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
