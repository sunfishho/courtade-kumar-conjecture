import InformationTheory.CourtadeKumar.RationalEnclosureCore

/-!
# Executable square-root certificate data

Only rational comparisons and squaring occur here.  The real square-root
soundness theorem lives in `ExactSqrtEnclosure`.
-/

namespace CourtadeKumar
namespace RationalEnclosure

/-- Claimed rational endpoints for a square-root enclosure. -/
structure SqrtCertificate where
  lower : ℚ
  upper : ℚ

/-- The checker verifies only rational comparisons and squaring. -/
def SqrtCertificate.check (input : RationalEnclosure)
    (certificate : SqrtCertificate) : Bool :=
  decide (
    0 ≤ input.lower ∧ input.lower ≤ input.upper ∧
    0 ≤ certificate.lower ∧ certificate.lower ^ 2 ≤ input.lower ∧
    0 ≤ certificate.upper ∧ input.upper ≤ certificate.upper ^ 2)

def SqrtCertificate.enclosure (certificate : SqrtCertificate) :
    RationalEnclosure :=
  ⟨certificate.lower, certificate.upper⟩

end RationalEnclosure
end CourtadeKumar
