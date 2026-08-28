import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk64 : Tree :=
  (.split .s (61/1600) (.split .k (29/32) (.split .chi (1/32) (.split .s (113/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (1/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .s (113/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird)) (.split .k (29/32) (.split .chi (1/32) (.split .s (131/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (1/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (1/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .s (131/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk64_generated_eq :
    buildEndpointTree 2 8 6 8
      (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (7/160)).lower .k (15/16)).lower .chi (1/16)) = some chunk64 := by
  rfl'

theorem chunk64_check :
    chunk64.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (7/160)).lower .k (15/16)).lower .chi (1/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 8 (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (7/160)).lower .k (15/16)).lower .chi (1/16)) chunk64 chunk64_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
