import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk10 : Tree :=
  (.split .chi (1/4) (.split .k (7/8) (.split .chi (1/8) (.split .k (13/16) (.split .chi (1/16) (.accept .endpointRetainedQ) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .chi (1/16) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (1/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (3/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.split .k (13/16) (.split .chi (3/16) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .chi (3/16) (.split .k (27/32) (.accept .endpointRetainedQ) (.split .chi (5/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.discard .xBelowHighShape)))) (.split .chi (1/8) (.split .k (15/16) (.split .chi (1/16) (.split .k (29/32) (.split .chi (1/32) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.discard .vBelowThird)) (.split .k (29/32) (.split .chi (3/32) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.discard .vBelowThird))) (.discard .vBelowThird)) (.split .k (15/16) (.split .chi (3/16) (.split .k (29/32) (.split .chi (5/32) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .chi (5/32) (.discard .vBelowThird) (.split .k (59/64) (.split .chi (11/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.discard .vBelowThird)))) (.discard .xBelowHighShape)) (.discard .vBelowThird)))) (.discard .xBelowHighShape))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk10_generated_eq :
    buildEndpointTree 2 8 6 14
      (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).upper .s (1/10000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)) = some chunk10 := by
  rfl'

theorem chunk10_check :
    chunk10.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).upper .s (1/10000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 14 (((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).upper .s (1/10000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)) chunk10 chunk10_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
