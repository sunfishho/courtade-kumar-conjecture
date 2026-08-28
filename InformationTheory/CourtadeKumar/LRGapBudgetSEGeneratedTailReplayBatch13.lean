import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk13 : Tree :=
  (.split .chi (1/4) (.split .k (5/8) (.split .chi (1/8) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (1/8) (.split .k (11/16) (.accept .endpointRetainedQ) (.split .chi (1/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (11/16) (.accept .endpointRetainedQ) (.split .chi (3/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.split .k (5/8) (.split .chi (3/8) (.accept .endpoint) (.accept .endpoint)) (.split .chi (3/8) (.split .k (11/16) (.accept .endpointRetainedQ) (.discard .xBelowHighShape)) (.discard .xBelowHighShape))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk13_generated_eq :
    buildEndpointTree 2 8 6 15
      ((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) = some chunk13 := by
  rfl'

theorem chunk13_check :
    chunk13.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 15 ((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).lower .k (3/4)) chunk13 chunk13_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
