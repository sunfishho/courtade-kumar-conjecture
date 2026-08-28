import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk107 : Tree :=
  (.split .k (29/32) (.split .chi (5/32) (.split .s (239/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (239/3200) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (57/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .chi (5/32) (.discard .vBelowThird) (.split .s (239/3200) (.split .k (59/64) (.split .chi (11/64) (.accept .endpointRetainedQ) (.discard .xBelowHighShape)) (.discard .vBelowThird)) (.split .k (59/64) (.split .chi (11/64) (.accept .endpointRetainedQ) (.discard .xBelowHighShape)) (.discard .vBelowThird)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk107_generated_eq :
    buildEndpointTree 2 8 6 7
      ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (31/400)).upper .k (7/8)).upper .chi (1/8)).upper .s (53/800)).lower .k (15/16)).lower .chi (3/16)).upper .s (23/320)) = some chunk107 := by
  rfl'

theorem chunk107_check :
    chunk107.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (31/400)).upper .k (7/8)).upper .chi (1/8)).upper .s (53/800)).lower .k (15/16)).lower .chi (3/16)).upper .s (23/320)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 7 ((((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (31/400)).upper .k (7/8)).upper .chi (1/8)).upper .s (53/800)).lower .k (15/16)).lower .chi (3/16)).upper .s (23/320)) chunk107 chunk107_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
