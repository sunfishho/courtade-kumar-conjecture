import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk59 : Tree :=
  (.split .s (79/1600) (.split .k (27/32) (.split .chi (3/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (3/32) (.split .s (149/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (149/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))) (.split .k (27/32) (.split .chi (3/32) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .chi (3/32) (.split .s (167/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))) (.split .s (167/3200) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ)) (.split .k (55/64) (.accept .endpointRetainedQ) (.accept .endpointRetainedQ))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk59_generated_eq :
    buildEndpointTree 2 8 6 8
      (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).lower .k (7/8)).lower .chi (1/8)).upper .s (7/160)).upper .k (13/16)).upper .chi (1/16)) = some chunk59 := by
  rfl'

theorem chunk59_check :
    chunk59.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).lower .k (7/8)).lower .chi (1/8)).upper .s (7/160)).upper .k (13/16)).upper .chi (1/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 8 (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).lower .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (13/400)).lower .k (7/8)).lower .chi (1/8)).upper .s (7/160)).upper .k (13/16)).upper .chi (1/16)) chunk59 chunk59_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
