import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk83 : Tree :=
  (.split .k (5/8) (.split .chi (1/8) (.split .s (71/800) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (71/800) (.split .k (9/16) (.accept .endpoint) (.accept .endpointRetainedQ)) (.split .k (9/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .chi (1/8) (.split .s (71/800) (.split .k (11/16) (.accept .endpointRetainedQ) (.split .chi (1/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (11/16) (.split .chi (1/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (1/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)))) (.split .s (71/800) (.split .k (11/16) (.split .chi (3/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (3/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .k (11/16) (.split .chi (3/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (3/16) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk83_generated_eq :
    buildEndpointTree 2 8 6 13
      ((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).lower .k (3/4)).lower .chi (1/4)).upper .s (31/400)) = some chunk83 := by
  rfl'

theorem chunk83_check :
    chunk83.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).lower .k (3/4)).lower .chi (1/4)).upper .s (31/400)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 13 ((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).lower .k (3/4)).lower .chi (1/4)).upper .s (31/400)) chunk83 chunk83_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
