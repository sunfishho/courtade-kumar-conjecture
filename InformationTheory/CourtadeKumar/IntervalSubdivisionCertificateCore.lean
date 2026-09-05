import InformationTheory.CourtadeKumar.RationalEnclosureCore

/-!
# Executable subdivision-certificate data

This module contains only exact rational data and Boolean computation.  The
interpretation of boxes and enclosures over `ℝ`, together with checker
soundness, lives in `IntervalSubdivisionCertificate`.
-/

namespace CourtadeKumar

/-- A rational closed box in the three cancellation coordinates. -/
structure CertificateBox where
  sLo : ℚ
  sHi : ℚ
  kLo : ℚ
  kHi : ℚ
  chiLo : ℚ
  chiHi : ℚ

/-- A decidable leaf test for a nonnegative lower endpoint. -/
def RationalEnclosure.provesNonnegative (interval : RationalEnclosure) : Bool :=
  decide (0 ≤ interval.lower)

/-- The coordinate along which a certificate node bisects its box. -/
inductive CertificateAxis where
  | s
  | k
  | chi
  deriving DecidableEq, Repr

/-- The closed child below a rational cut. -/
def CertificateBox.lower (box : CertificateBox)
    (axis : CertificateAxis) (cut : ℚ) : CertificateBox :=
  match axis with
  | .s => { box with sHi := cut }
  | .k => { box with kHi := cut }
  | .chi => { box with chiHi := cut }

/-- The closed child above a rational cut.  The children deliberately
overlap at the cut face. -/
def CertificateBox.upper (box : CertificateBox)
    (axis : CertificateAxis) (cut : ℚ) : CertificateBox :=
  match axis with
  | .s => { box with sLo := cut }
  | .k => { box with kLo := cut }
  | .chi => { box with chiLo := cut }

/-- A finite subdivision payload.  Its leaves contain only data consumed by
the trusted executable leaf checks. -/
inductive SubdivisionCertificate (AcceptData DiscardData : Type) where
  | accept (data : AcceptData)
  | discard (data : DiscardData)
  | split (axis : CertificateAxis) (cut : ℚ)
      (lower upper : SubdivisionCertificate AcceptData DiscardData)

/-- Boolean traversal of a subdivision certificate. -/
def SubdivisionCertificate.check
    {AcceptData DiscardData : Type}
    (acceptBox : CertificateBox → AcceptData → Bool)
    (discardBox : CertificateBox → DiscardData → Bool) :
    CertificateBox → SubdivisionCertificate AcceptData DiscardData → Bool
  | box, .accept data => acceptBox box data
  | box, .discard data => discardBox box data
  | box, .split axis cut lower upper =>
      check acceptBox discardBox (box.lower axis cut) lower &&
        check acceptBox discardBox (box.upper axis cut) upper

/-- Explicit name for the proof-free checker.  The established public
`check` API is itself defined in this core module; this alias lets semantic
adapter theorems state that fact without duplicating the computation. -/
def SubdivisionCertificate.coreCheck
    {AcceptData DiscardData : Type}
    (acceptBox : CertificateBox → AcceptData → Bool)
    (discardBox : CertificateBox → DiscardData → Bool)
    (box : CertificateBox)
    (certificate : SubdivisionCertificate AcceptData DiscardData) : Bool :=
  certificate.check acceptBox discardBox box

/-- Turn an executable interval extension into the acceptance Boolean used
at certificate leaves. -/
def enclosureAccepts
    {AcceptData : Type}
    (enclose : CertificateBox → AcceptData → RationalEnclosure)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  (enclose box data).provesNonnegative

end CourtadeKumar
