import AgentRootRatioBaseFacePilotData
import AgentRootRatioBaseFaceDominanceArithmetic

/-!
# Short rational data and independent checks for the base-face pilot

Numerical receipt modules can import this file without importing root-ratio
calculus or the semantic assembly.  Coverage soundness and the production
conclusion live in `AgentRootRatioBaseFaceRoundedPilot`.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioBaseFaceRoundedPilot

open RootRatioBaseFaceGroupedPilot

def coversCheck (outer inner : RationalEnclosure) : Bool :=
  decide (outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper)

/-! Each expensive numerical comparison has its own receipt boundary. -/

def FourBounds.bCoverCheck (bounds : FourBounds) (depth : ℕ) : Bool :=
  coversCheck bounds.b
    ((pilotPayload depth).evaluateAll pilotTerms (pilotBox depth)).b

def FourBounds.cBaseCoverCheck (bounds : FourBounds) (depth : ℕ) : Bool :=
  coversCheck bounds.cBase
    ((pilotPayload depth).evaluateAll pilotTerms (pilotBox depth)).cBase

def FourBounds.d1CoverCheck (bounds : FourBounds) (depth : ℕ) : Bool :=
  coversCheck bounds.d1
    ((pilotPayload depth).evaluateAll pilotTerms (pilotBox depth)).d1

def FourBounds.psiCoverCheck (bounds : FourBounds) (depth : ℕ) : Bool :=
  coversCheck bounds.psi
    ((pilotPayload depth).evaluateAll pilotTerms (pilotBox depth)).psi

end RootRatioBaseFaceRoundedPilot
end CourtadeKumar
