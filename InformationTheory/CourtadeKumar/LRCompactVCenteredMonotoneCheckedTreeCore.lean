import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneLeafCore

/-!
# Arithmetic-free assembly for centered-monotone compact-`V` leaves

Generated arithmetic modules authenticate accepted leaves independently.
This module packages those equalities as ordinary generic subdivision
certificates and joins them without replaying any leaf arithmetic.

The accepted-leaf checker binds the external subdivision box through
`Row.checkAt`.  The fixed certificate family has no discard leaves, so its
discard checker is constantly false.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVCenteredMonotoneCheckedTree

open LRCompactVCenteredMonotoneLeaf

/-- The centered-monotone certificate uses no physical-discard terminals. -/
def noDiscard (_box : CertificateBox) (_data : Unit) : Bool := false

/-- A generic subdivision certificate together with its already established
Boolean check.  The three term counts remain parameters so generated replay
data cannot silently change them during structural assembly. -/
structure CheckedTree
    (logTerms halfLogTerms dTerms : ℕ) (root : CertificateBox) : Type where
  certificate : SubdivisionCertificate Row Unit
  checked : certificate.check
    (Row.checkAt logTerms halfLogTerms dTerms) noDiscard root = true

namespace CheckedTree

/-- Package one independently kernel-checked accepted row. -/
def ofAccept
    (logTerms halfLogTerms dTerms : ℕ)
    {root : CertificateBox} (row : Row)
    (hcheck : Row.checkAt logTerms halfLogTerms dTerms root row = true) :
    CheckedTree logTerms halfLogTerms dTerms root where
  certificate := .accept row
  checked := hcheck

/-- Join two checked children at an exact generic subdivision split.  This
operation performs only Boolean conjunction on the existing proof objects. -/
def join
    {logTerms halfLogTerms dTerms : ℕ} {root : CertificateBox}
    (axis : CertificateAxis) (cut : ℚ)
    (lower : CheckedTree logTerms halfLogTerms dTerms
      (root.lower axis cut))
    (upper : CheckedTree logTerms halfLogTerms dTerms
      (root.upper axis cut)) :
    CheckedTree logTerms halfLogTerms dTerms root where
  certificate := .split axis cut lower.certificate upper.certificate
  checked := by
    simp only [SubdivisionCertificate.check, Bool.and_eq_true]
    exact ⟨lower.checked, upper.checked⟩

end CheckedTree
end LRCompactVCenteredMonotoneCheckedTree
end CourtadeKumar
