import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk65 : Tree :=
  (.split .k (29/32) (.split .chi (3/32) (.split .s (113/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (5/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (5/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .s (113/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (7/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (7/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk65_generated_eq :
    buildEndpointTree 2 8 6 7
      ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (7/160)).lower .k (15/16)).upper .chi (1/16)).lower .s (61/1600)) = some chunk65 := by
  rfl'

theorem chunk65_check :
    chunk65.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (7/160)).lower .k (15/16)).upper .chi (1/16)).lower .s (61/1600)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 7 ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (7/160)).lower .k (15/16)).upper .chi (1/16)).lower .s (61/1600)) chunk65 chunk65_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
