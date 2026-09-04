import InformationTheory.CourtadeKumar.RationalEnclosureCore
import Mathlib.Tactic.NormNum

/-!
# Small exact dominance arithmetic for the base-face pilot

This module authenticates only the literal rounded interval comparison.
It imports no D9 evaluator or root-ratio calculus. The separate numerical
coverage receipts are still required to connect these bounds to functions.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioBaseFaceRoundedPilot

structure FourBounds where
  b : RationalEnclosure
  cBase : RationalEnclosure
  d1 : RationalEnclosure
  psi : RationalEnclosure

def FourBounds.dominanceCheck (bounds : FourBounds) : Bool :=
  decide (
    (0 : ℚ) ≤ bounds.b.lower ∧
    bounds.cBase.upper ≤ (0 : ℚ) ∧
    (0 : ℚ) ≤ bounds.d1.lower ∧
    (0 : ℚ) ≤ bounds.psi.lower ∧
    -(bounds.b.upper * bounds.cBase.lower) ≤
      bounds.d1.lower * bounds.psi.lower)

/-- Exact 24-bit outward bounds proposed by the rational pilot.  Their
four coverage receipts are separate inputs; this definition does not assert
that the intervals enclose production values. -/
def pilot8Bounds : FourBounds where
  b := { lower := 23094793 / 16777216, upper := 23117261 / 16777216 }
  cBase := { lower := -370563 / 16777216, upper := -91261 / 4194304 }
  d1 := { lower := 1985895 / 16777216, upper := 2033171 / 16777216 }
  psi := { lower := 1138331 / 4194304, upper := 4596343 / 16777216 }

/-- This comparison uses only short rational endpoints.  Its positive
margin is `476021777037 / 281474976710656`. -/
theorem pilot8Bounds_dominance : pilot8Bounds.dominanceCheck = true := by
  norm_num [FourBounds.dominanceCheck, pilot8Bounds]

#print axioms CourtadeKumar.RootRatioBaseFaceRoundedPilot.pilot8Bounds_dominance

end RootRatioBaseFaceRoundedPilot
end CourtadeKumar
