import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeVAutoComputation

/-!
# Deterministic payload generation for high-shape `V` leaves

These functions merely propose rational square-root and logarithm payloads.
They are outside the trusted semantic argument: every generated field is
subsequently validated by the existing executable certificate checkers.
-/

namespace CourtadeKumar

namespace LRHighShapeVCertificate

/-- Acceptance with a generated payload; the unit argument lets this be used
with the generic subdivision datatype without storing payload records. -/
def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  accepts terms box (auto sqrtFuel logFuel box)

end LRHighShapeVCertificate

end CourtadeKumar
