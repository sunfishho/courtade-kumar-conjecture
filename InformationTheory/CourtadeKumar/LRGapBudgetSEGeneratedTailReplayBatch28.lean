import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk28 : Tree :=
  (.split .chi (1/8) (.split .s (7/160) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (7/160) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk28_generated_eq :
    buildEndpointTree 2 8 6 12
      (((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).lower .k (3/4)).lower .chi (1/4)).upper .s (13/400)).lower .k (5/8)) = some chunk28 := by
  rfl'

theorem chunk28_check :
    chunk28.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).lower .k (3/4)).lower .chi (1/4)).upper .s (13/400)).lower .k (5/8)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 12 (((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).lower .k (3/4)).lower .chi (1/4)).upper .s (13/400)).lower .k (5/8)) chunk28 chunk28_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
