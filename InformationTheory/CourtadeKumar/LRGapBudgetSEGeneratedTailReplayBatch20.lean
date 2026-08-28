import InformationTheory.CourtadeKumar.LRGapBudgetSECombinedAutoTree

namespace CourtadeKumar
namespace LRGapBudgetSEGeneratedTailReplay

open LRGapBudgetSECombinedAutoTree

def chunk20 : Tree :=
  (.discard .xBelowHighShape)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk20_generated_eq :
    buildEndpointTree 2 8 6 10
      (((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).lower .k (15/16)).upper .chi (3/16)) = some chunk20 := by
  rfl'

theorem chunk20_check :
    chunk20.check
      (LRGapBudgetSEDerivativeAcceptData.check 2 8 6)
      lrGapBudgetSEDiscardCheck (((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).lower .k (15/16)).upper .chi (3/16)) = true :=
  buildEndpointTree_check_of_eq 2 8 6 10 (((((((((((lrGapBudgetSETailRoot).lower .s (1/100)).upper .s (1/1000)).upper .k (1/2)).lower .chi (1/2)).upper .k (3/4)).lower .chi (1/4)).upper .k (7/8)).upper .chi (1/8)).lower .k (15/16)).upper .chi (3/16)) chunk20 chunk20_generated_eq

end LRGapBudgetSEGeneratedTailReplay
end CourtadeKumar
