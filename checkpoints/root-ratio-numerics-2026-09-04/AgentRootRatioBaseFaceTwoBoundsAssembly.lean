import AgentRootRatioBaseFaceBStandalone

/-!
# Small first-bracket assembly with only Cbase and Psi bounds outstanding

This is an explicit conditional theorem about the displayed scalar formulas.
B and D1 bounds are supplied by checked numerical proofs, not hypotheses.
Identifying the production Cbase/Psi formulas and proving their two interval
containments remain necessary before this can prove the production reserve.
-/

set_option autoImplicit false

namespace CourtadeKumar.RootRatioBaseFaceTwoBoundsAssembly

open RationalEnclosure RootRatioBaseFaceRoundedPilot RootRatioBaseFaceD1Standalone
open RootRatioBaseFaceBStandalone

theorem nonnegative_of_remaining_bounds {s k chi c psi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hchi : chiI.Contains chi)
    (hc : pilot8Bounds.cBase.Contains c)
    (hp : pilot8Bounds.psi.Contains psi) :
    0 ≤ bValue s k chi * c + d1Value s k * psi := by
  have hb := RootRatioBaseFaceBStandalone.rounded_contains hs hk hchi
  have hd := RootRatioBaseFaceD1Standalone.rounded_contains hs hk
  norm_num [pilot8Bounds, Contains] at hb hd hc hp
  have hb0 : 0 ≤ bValue s k chi := by linarith [hb.1]
  have hd0 : 0 ≤ d1Value s k := by linarith [hd.1]
  have hbc : (23117261 / 16777216 : ℝ) * (-(370563 / 16777216)) ≤
      bValue s k chi * c := calc
    _ ≤ bValue s k chi * (-(370563 / 16777216)) :=
      mul_le_mul_of_nonpos_right hb.2 (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.1 hb0
  have hdp : (1985895 / 16777216 : ℝ) * (1138331 / 4194304) ≤
      d1Value s k * psi :=
    mul_le_mul hd.1 hp.1 (by norm_num) hd0
  nlinarith only [hbc, hdp]

#print axioms CourtadeKumar.RootRatioBaseFaceTwoBoundsAssembly.nonnegative_of_remaining_bounds

end CourtadeKumar.RootRatioBaseFaceTwoBoundsAssembly
