import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk43 : Tree :=
  (.split .s (43/1600) (.split .k (29/32) (.split .chi (1/32) (.split .s (77/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (77/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird)) (.split .k (29/32) (.split .chi (1/32) (.split .s (19/640) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (19/640) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk43_generated_eq :
    buildEndpointTree 2 8 6 8
      (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (17/800)).lower .k (15/16)).lower .chi (1/16)) = some chunk43 := by
  rfl'

theorem chunk43_check :
    chunk43.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (17/800)).lower .k (15/16)).lower .chi (1/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 8 (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).upper .k (7/8)).lower .chi (1/8)).upper .s (17/800)).lower .k (15/16)).lower .chi (1/16)) chunk43 chunk43_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
