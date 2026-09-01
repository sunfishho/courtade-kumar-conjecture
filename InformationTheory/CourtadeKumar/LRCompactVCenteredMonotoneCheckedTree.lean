import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneCheckedTreeCore
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneLeafSound

/-!
# Semantic assembly for centered-monotone compact-`V` certificates

This module turns an arithmetically checked generic subdivision tree into the
uniform reserve inequality.  Accepted leaves use `Row.soundAt`, whose checker
first authenticates the externally reconstructed leaf box.  Discard
soundness is vacuous because this fixed certificate family has no discards.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVCenteredMonotoneCheckedTree

open LRCompactVCenteredMonotoneLeaf

namespace CheckedTree

/-- Semantic consequence of an assembled centered-monotone checked tree. -/
theorem target_nonnegative
    {logTerms halfLogTerms dTerms : ℕ} {root : CertificateBox}
    (tree : CheckedTree logTerms halfLogTerms dTerms root) :
    ∀ point, root.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hstruct := CourtadeKumar.subdivisionCertificate_sound
    (Relevant := LRCompactVPhysical)
    (Property := fun point ↦ LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point)
    (acceptBox := Row.checkAt logTerms halfLogTerms dTerms)
    (discardBox := noDiscard)
    (box := root) (certificate := tree.certificate)
    (fun leaf row hleaf point hpoint hphysical ↦
      Row.soundAt logTerms halfLogTerms dTerms hleaf
        point hpoint hphysical)
    (by
      intro leaf data hfalse
      simp [noDiscard] at hfalse)
    tree.checked
  intro point hpoint hphysical
  exact hstruct point hpoint hphysical hphysical

end CheckedTree
end LRCompactVCenteredMonotoneCheckedTree
end CourtadeKumar
