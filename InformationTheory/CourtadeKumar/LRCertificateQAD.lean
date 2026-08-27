import InformationTheory.CourtadeKumar.LRCertificateQEnclosure
import InformationTheory.CourtadeKumar.IntervalADArithmetic

/-!
# Verified interval-AD nodes for the LR entropy scalar

These nodes connect the target-specific endpoint checkers for `Q`, `Q'`, and
`Q''` to the generic three-coordinate interval automatic differentiation
engine.  The data generator remains untrusted; successful Boolean checks and
the ordinary chain rule establish all semantic derivative enclosures.
-/

namespace CourtadeKumar

/-- Payload for evaluating `Q ∘ y` and its three coordinate derivatives. -/
structure LRQADCertificate where
  value : LRQIntervalCertificate
  slope : LRQPrimeIntervalCertificate

namespace LRQADCertificate

def check (input : RationalEnclosure) (certificate : LRQADCertificate) : Bool :=
  certificate.value.check input && certificate.slope.check input

def evaluate (terms : ℕ) (certificate : LRQADCertificate)
    (input : IntervalAD) : IntervalAD :=
  IntervalAD.unary (certificate.value.enclosure terms)
    (certificate.slope.enclosure terms) input

theorem sound (terms : ℕ) {certificate : LRQADCertificate}
    {input : IntervalAD} {y derivS derivK derivChi : ℝ}
    (hcheck : certificate.check input.value = true)
    (hinput : input.Contains y derivS derivK derivChi) :
    (certificate.evaluate terms input).Contains
      (lrCertificateQ y)
      (lrCertificateQPrime y * derivS)
      (lrCertificateQPrime y * derivK)
      (lrCertificateQPrime y * derivChi) := by
  have hparts : certificate.value.check input.value = true ∧
      certificate.slope.check input.value = true := by
    simpa [check] using hcheck
  have hvalue := certificate.value.sound terms hparts.1 hinput.1
  have hslope := certificate.slope.sound terms hparts.2 hinput.1
  exact IntervalAD.contains_unary hvalue hslope hinput

end LRQADCertificate

/-- Payload for evaluating `Q' ∘ y`; the universal `(C3)` interval supplies
the scalar derivative `Q''`. -/
structure LRQPrimeADCertificate where
  value : LRQPrimeIntervalCertificate

namespace LRQPrimeADCertificate

def check (input : RationalEnclosure)
    (certificate : LRQPrimeADCertificate) : Bool :=
  certificate.value.check input && lrQSecondCoarseCheck input

def evaluate (terms : ℕ) (certificate : LRQPrimeADCertificate)
    (input : IntervalAD) : IntervalAD :=
  IntervalAD.unary (certificate.value.enclosure terms)
    (lrQSecondCoarseEnclosure input.value) input

theorem sound (terms : ℕ) {certificate : LRQPrimeADCertificate}
    {input : IntervalAD} {y derivS derivK derivChi : ℝ}
    (hcheck : certificate.check input.value = true)
    (hinput : input.Contains y derivS derivK derivChi) :
    (certificate.evaluate terms input).Contains
      (lrCertificateQPrime y)
      (lrCertificateQSecond y * derivS)
      (lrCertificateQSecond y * derivK)
      (lrCertificateQSecond y * derivChi) := by
  have hparts : certificate.value.check input.value = true ∧
      lrQSecondCoarseCheck input.value = true := by
    simpa [check] using hcheck
  have hvalue := certificate.value.sound terms hparts.1 hinput.1
  have hslope := lrQSecondCoarseEnclosure_sound hparts.2 hinput.1
  exact IntervalAD.contains_unary hvalue hslope hinput

end LRQPrimeADCertificate
end CourtadeKumar
