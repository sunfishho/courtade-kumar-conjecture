import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk136 : Tree :=
  (.split .s (11/200) (.split .k (3/4) (.discard .xBelowHighShape) (.discard .xBelowHighShape)) (.split .k (3/4) (.discard .xBelowHighShape) (.discard .xBelowHighShape)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk136_generated_eq :
    buildEndpointTree 2 8 6 17
      ((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).upper .chi (1/2)) = some chunk136 := by
  rfl'

theorem chunk136_check :
    chunk136.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck ((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).upper .chi (1/2)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 17 ((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).upper .chi (1/2)) chunk136 chunk136_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
