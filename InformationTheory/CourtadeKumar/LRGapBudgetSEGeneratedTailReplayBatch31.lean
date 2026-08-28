import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk31 : Tree :=
  (.split .chi (1/16) (.split .s (1/64) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (1/64) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (25/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk31_generated_eq :
    buildEndpointTree 2 8 6 9
      ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).lower .chi (1/8)).lower .s (17/800)).lower .k (13/16)) = some chunk31 := by
  rfl'

theorem chunk31_check :
    chunk31.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).lower .chi (1/8)).lower .s (17/800)).lower .k (13/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 9 ((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).lower .s (13/400)).lower .k (7/8)).lower .chi (1/8)).lower .s (17/800)).lower .k (13/16)) chunk31 chunk31_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
