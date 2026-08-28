import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk39 : Tree :=
  (.split .chi (3/16) (.split .s (43/1600) (.split .k (27/32) (.split .chi (5/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (5/32) (.split .s (77/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (77/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.split .k (27/32) (.split .chi (5/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (5/32) (.split .s (19/640) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (19/640) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))))) (.discard .xBelowHighShape))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk39_generated_eq :
    buildEndpointTree 2 8 6 9
      ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).upper .chi (1/8)).upper .s (17/800)).upper .k (13/16)) = some chunk39 := by
  rfl'

theorem chunk39_check :
    chunk39.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).upper .chi (1/8)).upper .s (17/800)).upper .k (13/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 9 ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).upper .chi (1/8)).upper .s (17/800)).upper .k (13/16)) chunk39 chunk39_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
