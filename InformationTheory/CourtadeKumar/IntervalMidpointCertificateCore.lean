import InformationTheory.CourtadeKumar.ExactIntervalArithmeticCore
import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificateCore

/-!
# Executable midpoint-certificate data

This module contains the exact rational midpoint lower-bound computation and
its Boolean check.  Its real-valued interpretation and soundness theorem live
in `IntervalMidpointCertificate`.
-/

namespace CourtadeKumar

def CertificateBox.sInterval (box : CertificateBox) : RationalEnclosure :=
  ⟨box.sLo, box.sHi⟩

def CertificateBox.kInterval (box : CertificateBox) : RationalEnclosure :=
  ⟨box.kLo, box.kHi⟩

def CertificateBox.chiInterval (box : CertificateBox) : RationalEnclosure :=
  ⟨box.chiLo, box.chiHi⟩

/-- The absolute-value bound represented by a derivative enclosure. -/
def RationalEnclosure.maxAbs (interval : RationalEnclosure) : ℚ :=
  max |interval.lower| |interval.upper|

/-- The exact rational data recomputed at a midpoint-form accepted leaf. -/
structure MidpointCertificate where
  value : RationalEnclosure
  derivS : RationalEnclosure
  derivK : RationalEnclosure
  derivChi : RationalEnclosure

/-- Rational lower bound obtained from the midpoint value minus the three
derivative-radius losses. -/
def MidpointCertificate.lowerBound
    (box : CertificateBox) (certificate : MidpointCertificate) : ℚ :=
  certificate.value.lower -
    certificate.derivS.maxAbs * RationalEnclosure.radius box.sInterval -
    certificate.derivK.maxAbs * RationalEnclosure.radius box.kInterval -
    certificate.derivChi.maxAbs * RationalEnclosure.radius box.chiInterval

def MidpointCertificate.check
    (box : CertificateBox) (certificate : MidpointCertificate) : Bool :=
  decide (0 < certificate.lowerBound box)

/-- Explicit name for the proof-free midpoint check.  The public `check` API
is defined above in this core module. -/
def MidpointCertificate.coreCheck
    (box : CertificateBox) (certificate : MidpointCertificate) : Bool :=
  certificate.check box

end CourtadeKumar
