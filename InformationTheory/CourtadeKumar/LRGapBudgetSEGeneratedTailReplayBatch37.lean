import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk37 : Tree :=
  (.split .k (13/16) (.split .chi (3/16) (.split .s (1/64) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (1/64) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .chi (3/16) (.split .s (1/64) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (5/32) (.accept .endpointRetainedQ) (.split .s (41/3200) (.accept .endpointRetainedQ) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.split .k (27/32) (.split .chi (5/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (5/32) (.split .s (59/3200) (.accept .endpointRetainedQ) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (59/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))))) (.discard .xBelowHighShape)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk37_generated_eq :
    buildEndpointTree 2 8 6 10
      (((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).upper .chi (1/8)).lower .s (17/800)) = some chunk37 := by
  rfl'

theorem chunk37_check :
    chunk37.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).upper .chi (1/8)).lower .s (17/800)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 10 (((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).upper .chi (1/8)).lower .s (17/800)) chunk37 chunk37_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
