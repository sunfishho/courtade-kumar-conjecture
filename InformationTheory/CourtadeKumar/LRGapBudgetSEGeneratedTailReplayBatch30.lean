import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk30 : Tree :=
  (.split .s (13/400) (.split .k (5/8) (.split .chi (3/8) (.split .s (17/800) (.accept .endpointRetainedQ) (.split .k (9/16) (.accept .endpoint) (.accept .endpointRetainedQ))) (.discard .xBelowHighShape)) (.split .chi (3/8) (.split .s (17/800) (.split .k (11/16) (.accept .endpointRetainedQ) (.discard .xBelowHighShape)) (.split .k (11/16) (.accept .endpointRetainedQ) (.discard .xBelowHighShape))) (.discard .xBelowHighShape))) (.split .k (5/8) (.split .chi (3/8) (.split .s (7/160) (.split .k (9/16) (.accept .endpoint) (.accept .endpointRetainedQ)) (.split .k (9/16) (.accept .endpoint) (.accept .endpointRetainedQ))) (.discard .xBelowHighShape)) (.split .chi (3/8) (.split .s (7/160) (.split .k (11/16) (.discard .xBelowHighShape) (.discard .xBelowHighShape)) (.split .k (11/16) (.discard .xBelowHighShape) (.discard .xBelowHighShape))) (.discard .xBelowHighShape))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk30_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).lower .k (3/4)).upper .chi (1/4)) = some chunk30 := by
  rfl'

theorem chunk30_check :
    chunk30.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).lower .k (3/4)).upper .chi (1/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).lower .k (3/4)).upper .chi (1/4)) chunk30 chunk30_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
