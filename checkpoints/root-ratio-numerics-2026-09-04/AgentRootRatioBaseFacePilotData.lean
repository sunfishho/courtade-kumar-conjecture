import InformationTheory.CourtadeKumar.LRDeterminantFiniteD9Evaluator

/-!
# Arithmetic data for the base-face numerical pilot

This module deliberately omits the root-ratio calculus import.  Receipt
modules need only the existing exact evaluator and the closed data below.
Production-target soundness lives in `AgentRootRatioBaseFaceGroupedPilot`.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioBaseFaceGroupedPilot

def pilotBox (depth : ℕ) : CertificateBox where
  sLo := 1 / 16
  sHi := 1 / 16
  kLo := 3 - 1 / (2 : ℚ) ^ depth
  kHi := 3 + 1 / (2 : ℚ) ^ depth
  chiLo := 3 / 8 - 1 / (8 * (2 : ℚ) ^ depth)
  chiHi := 3 / 8 + 1 / (8 * (2 : ℚ) ^ depth)

def pilotTerms : ℕ := 8
def pilotSqrtFuel : ℕ := 12
def pilotLogFuel : ℕ := 8

def pilotPayload (depth : ℕ) : LRFiniteDeterminantD9ZeroFaceCertificate :=
  LRFiniteDeterminantD9ZeroFaceCertificate.auto
    pilotSqrtFuel pilotLogFuel (pilotBox depth)

def pilotPayloadCheck (depth : ℕ) : Bool :=
  (pilotPayload depth).payloadCheck (pilotBox depth)

def pilotDominanceCheck (depth : ℕ) : Bool :=
  (pilotPayload depth).firstBracketDominanceCheck pilotTerms (pilotBox depth)

def pilotCheck (depth : ℕ) : Bool :=
  pilotPayloadCheck depth && pilotDominanceCheck depth

end RootRatioBaseFaceGroupedPilot
end CourtadeKumar
