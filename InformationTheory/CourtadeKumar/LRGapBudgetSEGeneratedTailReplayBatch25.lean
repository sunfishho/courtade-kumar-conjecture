import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk25 : Tree :=
  (.split .k (1/4) (.split .chi (1/4) (.accept .endpoint) (.accept .endpoint)) (.split .chi (1/4) (.split .s (31/400) (.split .k (3/8) (.accept .endpoint) (.split .chi (1/8) (.accept .endpoint) (.accept .endpoint))) (.split .k (3/8) (.accept .endpoint) (.split .chi (1/8) (.accept .endpointRetainedQ) (.accept .endpoint)))) (.split .s (31/400) (.split .k (3/8) (.accept .endpoint) (.accept .endpoint)) (.split .k (3/8) (.accept .endpoint) (.split .chi (3/8) (.accept .endpoint) (.accept .endpoint))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk25_generated_eq :
    buildEndpointTree 2 8 6 16
      (((((lrGapBudgetSETailRoot).upper .s (1/100)).lower .k (1/2)).lower .chi (1/2)).upper .s (11/200)) = some chunk25 := by
  rfl'

theorem chunk25_check :
    chunk25.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((lrGapBudgetSETailRoot).upper .s (1/100)).lower .k (1/2)).lower .chi (1/2)).upper .s (11/200)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 16 (((((lrGapBudgetSETailRoot).upper .s (1/100)).lower .k (1/2)).lower .chi (1/2)).upper .s (11/200)) chunk25 chunk25_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
