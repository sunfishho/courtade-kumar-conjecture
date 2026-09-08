import InformationTheory.CourtadeKumar.LRHighShapeCoordinateAD
import InformationTheory.CourtadeKumar.LRDeterminantAutoCertificateCore

/-!
# Deterministic payload generation for high-shape coordinates

This lightweight module proposes the two rational square-root payloads used by
the verified high-shape coordinate map.  The proposal remains outside the
trusted semantic argument: `LRHighShapeCoordinateCertificate.check` validates
both fields before any soundness theorem uses them.
-/

namespace CourtadeKumar
namespace LRHighShapeCoordinateCertificate

def auto (sqrtFuel : ℕ) (box : CertificateBox) :
    LRHighShapeCoordinateCertificate :=
  { tSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
      (lrCertificateXAD box).value
    vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
      (lrCertificateVRadicandAD box).value }

end LRHighShapeCoordinateCertificate
end CourtadeKumar
