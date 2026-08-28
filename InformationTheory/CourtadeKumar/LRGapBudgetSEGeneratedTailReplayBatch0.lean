import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk0 : Tree :=
  (.split .chi (1/2) (.split .k (1/4) (.accept .endpoint) (.split .chi (1/4) (.accept .endpoint) (.accept .endpoint))) (.split .k (1/4) (.accept .endpoint) (.split .chi (3/4) (.accept .endpoint) (.accept .endpoint))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk0_generated_eq :
    buildEndpointTree 2 8 6 15
      ((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).lower .k (1/2)) = some chunk0 := by
  rfl'

theorem chunk0_check :
    chunk0.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).lower .k (1/2)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 15 ((((((lrGapBudgetSETailRoot).lower .s (1/100)).lower .s (1/1000)).lower .s (1/10000)).lower .s (1/100000)).lower .k (1/2)) chunk0 chunk0_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
