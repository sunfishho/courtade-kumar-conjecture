import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk133 : Tree :=
  (.discard .xBelowHighShape)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk133_generated_eq :
    buildEndpointTree 2 8 6 8
      (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).upper .chi (1/8)).upper .s (71/800)).lower .k (15/16)).upper .chi (3/16)) = some chunk133 := by
  rfl'

theorem chunk133_check :
    chunk133.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).upper .chi (1/8)).upper .s (71/800)).lower .k (15/16)).upper .chi (3/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 8 (((((((((((((lrGapBudgetSETailRoot).upper .s (1/100)).upper .k (1/2)).lower .chi (1/2)).upper .s (11/200)).upper .k (3/4)).lower .chi (1/4)).upper .s (31/400)).upper .k (7/8)).upper .chi (1/8)).upper .s (71/800)).lower .k (15/16)).upper .chi (3/16)) chunk133 chunk133_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
