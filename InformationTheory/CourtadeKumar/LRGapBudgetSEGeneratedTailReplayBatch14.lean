import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk14 : Tree :=
  (.split .chi (1/8) (.split .k (13/16) (.split .chi (1/16) (.split .s (11/2000) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (11/2000) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .chi (1/16) (.split .s (11/2000) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (1/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (1/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .s (11/2000) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (3/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (3/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))))) (.split .k (13/16) (.split .chi (3/16) (.split .s (11/2000) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (11/2000) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .chi (3/16) (.split .s (11/2000) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (5/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (5/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.discard .xBelowHighShape))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk14_generated_eq :
    buildEndpointTree 2 8 6 13
      ((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).lower .k (7/8)) = some chunk14 := by
  rfl'

theorem chunk14_check :
    chunk14.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).lower .k (7/8)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 13 ((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).lower .k (7/8)) chunk14 chunk14_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
