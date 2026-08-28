import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk120 : Tree :=
  (.split .s (133/1600) (.split .k (29/32) (.split .chi (1/32) (.split .s (257/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (257/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird)) (.split .k (29/32) (.split .chi (1/32) (.split .s (11/128) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (11/128) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (57/64) (.accept .endpointRetainedQ) (.split .chi (3/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.discard .vBelowThird)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk120_generated_eq :
    buildEndpointTree 2 8 6 8
      (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (71/800)).lower .k (15/16)).lower .chi (1/16)) = some chunk120 := by
  rfl'

theorem chunk120_check :
    chunk120.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (71/800)).lower .k (15/16)).lower .chi (1/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 8 (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).lower .chi (1/8)).lower .s (71/800)).lower .k (15/16)).lower .chi (1/16)) chunk120 chunk120_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
