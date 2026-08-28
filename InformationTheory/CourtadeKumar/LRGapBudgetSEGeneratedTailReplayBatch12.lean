import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk12 : Tree :=
  (.split .chi (1/2) (.split .k (1/4) (.accept .endpoint) (.split .chi (1/4) (.split .k (3/8) (.accept .endpoint) (.accept .endpoint)) (.accept .endpoint))) (.split .k (1/4) (.accept .endpoint) (.split .chi (3/4) (.accept .endpoint) (.accept .endpoint))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk12_generated_eq :
    buildEndpointTree 2 8 6 17
      ((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).lower .k (1/2)) = some chunk12 := by
  rfl'

theorem chunk12_check :
    chunk12.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).lower .k (1/2)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 17 ((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).lower .k (1/2)) chunk12 chunk12_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
