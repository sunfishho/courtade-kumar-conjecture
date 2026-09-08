import InformationTheory.CourtadeKumar.IntervalMidpointCertificateCore

/-!
# Executable leaf checks for assembled interval certificates

These definitions combine target-specific rational evaluators with the
generic proof-free checks.  Their semantic contracts and end-to-end
soundness theorems live in `IntervalCertificateAssembly`.
-/

namespace CourtadeKumar

def midpointLeafAccepts {AcceptData : Type}
    (evaluate : CertificateBox → AcceptData → MidpointCertificate)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  (evaluate box data).check box

/-- A checked midpoint leaf first validates its target-specific arithmetic
payload, then tests the generic midpoint lower bound. -/
def checkedMidpointLeafAccepts {AcceptData : Type}
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (evaluate : CertificateBox → AcceptData → MidpointCertificate)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  payloadCheck box data && (evaluate box data).check box

/-- A direct interval leaf with a separately checked transcendental payload.
This is useful when the interval extension over the whole leaf is already
sharp enough and no midpoint/derivative correction is needed. -/
def checkedEnclosureLeafAccepts {AcceptData : Type}
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (enclose : CertificateBox → AcceptData → RationalEnclosure)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  payloadCheck box data && (enclose box data).provesNonnegative

end CourtadeKumar
