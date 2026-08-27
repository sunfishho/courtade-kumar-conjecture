import InformationTheory.CourtadeKumar.LRCompactVPhysicalDiscard
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Deterministic payload generation for compact `V` leaves

These generators only propose logarithm range reductions.  Their output has
no trusted status until the compact Boolean leaf or discard checker accepts
it.
-/

namespace CourtadeKumar

namespace LRCompactVBCertificate

def auto (logFuel : ℕ) (box : CertificateBox) : LRCompactVBCertificate :=
  { logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOnePlusVEnclosure box)
    logOneSubRY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOneSubRYEnclosure box) }

end LRCompactVBCertificate

namespace LRCompactVLeafCertificate

def auto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVLeafCertificate :=
  { b := LRCompactVBCertificate.auto logFuel box }

end LRCompactVLeafCertificate

namespace LRCompactVDiscardCertificate

def auto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVDiscardCertificate :=
  { b := LRCompactVBCertificate.auto logFuel box
    logOneSubY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOneSubYEnclosure box) }

end LRCompactVDiscardCertificate

end CourtadeKumar
