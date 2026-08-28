import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk15 : Tree :=
  (.split .s (11/2000) (.split .k (29/32) (.split .chi (1/32) (.split .s (13/4000) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (13/4000) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.discard .vBelowThird)) (.split .k (29/32) (.split .chi (1/32) (.split .s (31/4000) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (31/4000) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.discard .vBelowThird)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk15_generated_eq :
    buildEndpointTree 2 8 6 10
      (((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).lower .chi (1/8)).lower .k (15/16)).lower .chi (1/16)) = some chunk15 := by
  rfl'

theorem chunk15_check :
    chunk15.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).lower .chi (1/8)).lower .k (15/16)).lower .chi (1/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 10 (((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).lower .chi (1/8)).lower .k (15/16)).lower .chi (1/16)) chunk15 chunk15_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
