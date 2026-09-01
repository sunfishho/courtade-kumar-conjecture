import InformationTheory.CourtadeKumar.LRCompactVStagedGroupedGeneratedCertificate

/-!
# Arithmetic-free assembly for staged compact-`V` certificates

Each generated terminal module authenticates one leaf or discard Boolean with
the ordinary kernel and exports a `CheckedTree` at its literal box.  Structural
modules combine those already-proved semantic objects, so joining a large tree
does not replay any terminal arithmetic.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVStagedGroupedCheckedTree

/-- The semantic result exported by every independently checked terminal and
every structural component. -/
structure CheckedTree (root : CertificateBox) : Type where
  target_nonnegative :
    ∀ point, root.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point

/-- Package an accepted terminal after its one arithmetic Boolean has been
checked by the kernel. -/
def ofAccept
    (logTerms pZeroTerms wTerms dTerms directN : ℕ)
    {root : CertificateBox}
    (certificate : LRCompactVStagedGroupedLeafCertificate)
    (hcheck : certificate.check
      logTerms pZeroTerms wTerms dTerms directN root = true) :
    CheckedTree root :=
  ⟨certificate.sound
    logTerms pZeroTerms wTerms dTerms directN hcheck⟩

/-- Package a physically impossible terminal after its one discard Boolean
has been checked by the kernel. -/
def ofDiscard
    (logTerms : ℕ) {root : CertificateBox}
    (certificate : LRCompactVDiscardCertificate)
    (hcheck : certificate.check logTerms root = true) :
    CheckedTree root :=
  ⟨by
    intro point hpoint hphysical
    exact (certificate.excludes_physical
      logTerms hcheck point hpoint hphysical).elim⟩

/-- Combine two already checked children.  This operation performs only the
geometric case split at the shared rational cut. -/
def join {root : CertificateBox}
    (axis : CertificateAxis) (cut : ℚ)
    (lower : CheckedTree (root.lower axis cut))
    (upper : CheckedTree (root.upper axis cut)) :
    CheckedTree root :=
  ⟨by
    intro point hpoint hphysical
    rcases root.contains_lower_or_upper hpoint axis cut with
      hLower | hUpper
    · exact lower.target_nonnegative point hLower hphysical
    · exact upper.target_nonnegative point hUpper hphysical⟩

/-- Literal-box adapter used by generated structural modules.  Each binding
is local to one split, preventing normalization through a long root-to-leaf
path. -/
def joinLiteral
    (root lowerRoot upperRoot : CertificateBox)
    (axis : CertificateAxis) (cut : ℚ)
    (lowerBinding : root.lower axis cut = lowerRoot)
    (upperBinding : root.upper axis cut = upperRoot)
    (lower : CheckedTree lowerRoot)
    (upper : CheckedTree upperRoot) : CheckedTree root := by
  subst lowerRoot
  subst upperRoot
  exact join axis cut lower upper

end LRCompactVStagedGroupedCheckedTree
end CourtadeKumar
