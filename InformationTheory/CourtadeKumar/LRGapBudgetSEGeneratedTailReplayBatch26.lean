import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk26 : Tree :=
  (.split .s (11/200) (.split .k (1/4) (.accept .endpoint) (.split .chi (3/4) (.split .s (13/400) (.split .k (3/8) (.accept .endpoint) (.accept .endpoint)) (.split .k (3/8) (.accept .endpoint) (.accept .endpoint))) (.discard .xBelowHighShape))) (.split .k (1/4) (.accept .endpoint) (.split .chi (3/4) (.split .s (31/400) (.split .k (3/8) (.accept .endpoint) (.accept .endpoint)) (.split .k (3/8) (.accept .endpoint) (.accept .endpoint))) (.discard .xBelowHighShape))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk26_generated_eq :
    buildEndpointTree 2 8 6 17
      ((((lrGapBudgetSETailRoot).upper .s (1/100)).lower .k (1/2)).upper .chi (1/2)) = some chunk26 := by
  rfl'

theorem chunk26_check :
    chunk26.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((lrGapBudgetSETailRoot).upper .s (1/100)).lower .k (1/2)).upper .chi (1/2)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 17 ((((lrGapBudgetSETailRoot).upper .s (1/100)).lower .k (1/2)).upper .chi (1/2)) chunk26 chunk26_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
