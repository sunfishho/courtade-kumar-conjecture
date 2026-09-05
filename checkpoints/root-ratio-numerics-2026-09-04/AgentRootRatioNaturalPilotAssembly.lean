import AgentRootRatioNaturalComponents
import AgentRootRatioBaseFaceD1Sharp

/-!
# Direct positive first-bracket inequality on the depth-eight pilot box

Every numerical bound is supplied by a checked theorem. No Cbase/Psi
enclosure hypotheses, corner lemmas, or automatic payload premises remain.
This theorem concerns the explicit scalar formulas below; connecting their
names to the full production assembly remains a separate integration task.
It covers ONE box, not the complete base-face region or the CK theorem.
-/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalPilotAssembly
open RationalEnclosure RootRatioBaseFaceRoundedPilot RootRatioBaseFaceD1Standalone
open RootRatioBaseFaceBStandalone RootRatioNaturalComponents

theorem firstBracket_positive {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hchi : chiI.Contains chi) :
    0 < bValue s k chi * cValue s k chi + d1Value s k * psiValue s k chi := by
  have hb := RootRatioBaseFaceBStandalone.rounded_contains hs hk hchi
  have hd := RootRatioBaseFaceD1Sharp.rounded_contains hs hk
  have hc := c_contains hs hk hchi
  have hp := psi_contains hs hk hchi
  norm_num [pilot8Bounds, RootRatioBaseFaceD1Sharp.bounds, cBounds, psiBounds,
    Contains] at hb hd hc hp
  have hb0 : 0 ≤ bValue s k chi := by linarith [hb.1]
  have hd0 : 0 ≤ d1Value s k := by linarith [hd.1]
  have hbc : (23117261 / 16777216 : ℝ) * (-(12235 / 524288)) ≤
      bValue s k chi * cValue s k chi := calc
    _ ≤ bValue s k chi * (-(12235 / 524288)) :=
      mul_le_mul_of_nonpos_right hb.2 (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.1 hb0
  have hdp : (1003077 / 8388608 : ℝ) * (2277261 / 8388608) ≤
      d1Value s k * psiValue s k chi :=
    mul_le_mul hd.1 hp.1 (by norm_num) hd0
  nlinarith only [hbc, hdp]

theorem pilot_positive (k chi : ℝ)
    (hk : (767 / 256 : ℝ) ≤ k ∧ k ≤ 769 / 256)
    (hchi : (767 / 2048 : ℝ) ≤ chi ∧ chi ≤ 769 / 2048) :
    0 < bValue (1 / 16) k chi * cValue (1 / 16) k chi +
      d1Value (1 / 16) k * psiValue (1 / 16) k chi := by
  apply firstBracket_positive
  · norm_num [sI, point, Contains]
  · simpa [kI, Contains] using hk
  · simpa [chiI, Contains] using hchi

#print axioms CourtadeKumar.RootRatioNaturalPilotAssembly.firstBracket_positive
#print axioms CourtadeKumar.RootRatioNaturalPilotAssembly.pilot_positive
end CourtadeKumar.RootRatioNaturalPilotAssembly
