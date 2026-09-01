import InformationTheory.CourtadeKumar.LRDeterminantFiniteD9CenteredEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteD9SemanticTree

/-!
# Hybrid direct/centered checked trees for restricted finite D9

The untrusted topology chooses a tiny tag at each accepted leaf.  A fallback
leaf uses the established whole-box D9 enclosure (including its zero-face
variant); a centered leaf evaluates the value at the exact rational midpoint
and its derivatives on the whole box.  Both tags are checked against the
external leaf box by executable Boolean predicates.

The recoverable `CheckedTree` wrapper lets generated arithmetic chunks prove
one terminal at a time and lets later assembly modules join those opaque
children without replaying interval arithmetic.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRFiniteDeterminantRestrictedD9HybridPayloadFree

inductive AcceptKind where
  | fallback
  | zeroFace
  | centered
  deriving DecidableEq, Repr

abbrev Tree := SubdivisionCertificate AcceptKind Unit

def acceptCheck (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : AcceptKind → Bool
  | .fallback =>
      LRFiniteDeterminantD9PayloadFree.accepts
        terms sqrtFuel logFuel box ()
  | .zeroFace =>
      let certificate := LRFiniteDeterminantD9ZeroFaceCertificate.auto
        sqrtFuel logFuel box
      LRFiniteDeterminantD9ZeroFaceCertificate.payloadCheck box certificate &&
        certificate.componentCheck terms box
  | .centered =>
      LRFiniteDeterminantD9CenteredCertificate.autoAccepts
        terms sqrtFuel logFuel box ()

theorem acceptCheck_sound (terms sqrtFuel logFuel : Nat) :
    LRFiniteDeterminantRestrictedD9AcceptCompatible
      (acceptCheck terms sqrtFuel logFuel) := by
  intro box data hcheck point hpoint
  cases data with
  | fallback =>
      have hparts :
          LRFiniteDeterminantD9PayloadFree.payloadCheck
              terms sqrtFuel logFuel box () = true ∧
            (LRFiniteDeterminantD9PayloadFree.enclose
              terms sqrtFuel logFuel box ()).provesNonnegative = true := by
        simpa [acceptCheck, LRFiniteDeterminantD9PayloadFree.accepts,
          checkedEnclosureLeafAccepts] using hcheck
      exact RationalEnclosure.nonnegative_of_provesNonnegative hparts.2
        ((LRFiniteDeterminantD9PayloadFree.evaluatorSound
          terms sqrtFuel logFuel).value box () hparts.1 point hpoint)
  | zeroFace =>
      let certificate := LRFiniteDeterminantD9ZeroFaceCertificate.auto
        sqrtFuel logFuel box
      have hparts :
          LRFiniteDeterminantD9ZeroFaceCertificate.payloadCheck
              box certificate = true ∧
            certificate.componentCheck terms box = true := by
        simpa [acceptCheck, certificate] using hcheck
      exact certificate.nonnegative_of_payload_and_componentCheck
        terms hpoint hparts.1 hparts.2
  | centered =>
      let certificate := LRFiniteDeterminantD9CenteredCertificate.auto
        sqrtFuel logFuel box
      have hparts :
          LRFiniteDeterminantD9CenteredCertificate.payloadCheck
              box certificate = true ∧
            (LRFiniteDeterminantD9CenteredCertificate.evaluate
              terms box certificate).check box = true := by
        simpa [acceptCheck,
          LRFiniteDeterminantD9CenteredCertificate.autoAccepts,
          LRFiniteDeterminantD9CenteredCertificate.accepts,
          checkedMidpointLeafAccepts, certificate] using hcheck
      exact (MidpointCertificate.sound_of_derivativeEnclosures
        ((LRFiniteDeterminantD9CenteredCertificate.checkedEvaluatorSound
          terms).value box certificate hparts.1)
        ((LRFiniteDeterminantD9CenteredCertificate.checkedEvaluatorSound
          terms).derivatives box certificate hparts.1)
        hparts.2 hpoint).le

def discardCheck (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (data : Unit) : Bool :=
  LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck
    terms sqrtFuel logFuel box data

theorem discardCheck_sound (terms sqrtFuel logFuel : Nat) :
    LRFiniteDeterminantRestrictedRawDiscardCompatible
      (discardCheck terms sqrtFuel logFuel) := by
  intro box data hcheck
  exact LRFiniteDeterminantRestrictedD9PayloadFree.discardCheck_sound
    terms sqrtFuel logFuel box data hcheck

def toSemanticCheckedTree (terms sqrtFuel logFuel : Nat)
    {root : CertificateBox} (tree : Tree)
    (hcheck : tree.check (acceptCheck terms sqrtFuel logFuel)
      (discardCheck terms sqrtFuel logFuel) root = true) :
    LRFiniteDeterminantRestrictedSemanticD9CheckedTree root where
  AcceptData := AcceptKind
  DiscardData := Unit
  acceptCheck := acceptCheck terms sqrtFuel logFuel
  discardCheck := discardCheck terms sqrtFuel logFuel
  acceptCompatible := acceptCheck_sound terms sqrtFuel logFuel
  discardCompatible := discardCheck_sound terms sqrtFuel logFuel
  certificate := tree
  checked := hcheck

structure CheckedTree
    (terms sqrtFuel logFuel : Nat) (root : CertificateBox) : Type where
  certificate : Tree
  checked : certificate.check (acceptCheck terms sqrtFuel logFuel)
    (discardCheck terms sqrtFuel logFuel) root = true

abbrev CheckedChunk := CheckedTree

namespace CheckedTree

def ofAccept
    (terms sqrtFuel logFuel : Nat) {root : CertificateBox}
    (kind : AcceptKind)
    (hcheck : acceptCheck terms sqrtFuel logFuel root kind = true) :
    CheckedTree terms sqrtFuel logFuel root where
  certificate := .accept kind
  checked := hcheck

def ofDiscard
    (terms sqrtFuel logFuel : Nat) {root : CertificateBox}
    (hcheck : discardCheck terms sqrtFuel logFuel root () = true) :
    CheckedTree terms sqrtFuel logFuel root where
  certificate := .discard ()
  checked := hcheck

def join
    {terms sqrtFuel logFuel : Nat} {root : CertificateBox}
    (axis : CertificateAxis) (cut : ℚ)
    (lower : CheckedTree terms sqrtFuel logFuel
      (root.lower axis cut))
    (upper : CheckedTree terms sqrtFuel logFuel
      (root.upper axis cut)) :
    CheckedTree terms sqrtFuel logFuel root where
  certificate := .split axis cut lower.certificate upper.certificate
  checked := by
    simp only [SubdivisionCertificate.check, Bool.and_eq_true]
    exact ⟨lower.checked, upper.checked⟩

def joinLiteral
    {terms sqrtFuel logFuel : Nat}
    (root lowerRoot upperRoot : CertificateBox)
    (axis : CertificateAxis) (cut : ℚ)
    (lowerBinding : root.lower axis cut = lowerRoot)
    (upperBinding : root.upper axis cut = upperRoot)
    (lower : CheckedTree terms sqrtFuel logFuel lowerRoot)
    (upper : CheckedTree terms sqrtFuel logFuel upperRoot) :
    CheckedTree terms sqrtFuel logFuel root := by
  subst lowerRoot
  subst upperRoot
  exact join axis cut lower upper

def toSemanticCheckedTree
    {terms sqrtFuel logFuel : Nat} {root : CertificateBox}
    (tree : CheckedTree terms sqrtFuel logFuel root) :
    LRFiniteDeterminantRestrictedSemanticD9CheckedTree root :=
  LRFiniteDeterminantRestrictedD9HybridPayloadFree.toSemanticCheckedTree
    terms sqrtFuel logFuel tree.certificate tree.checked

theorem target_nonnegative
    {terms sqrtFuel logFuel : Nat} {root : CertificateBox}
    (tree : CheckedTree terms sqrtFuel logFuel root)
    {point : CertificatePoint}
    (hpoint : root.Contains point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsk : point.s < point.k) :
    0 ≤ lrFiniteDeterminantD9ReplayTarget point :=
  tree.toSemanticCheckedTree.target_nonnegative hpoint hrelevant hsk

theorem fixed16Region_certificate
    {terms sqrtFuel logFuel : Nat}
    (tree : CheckedTree terms sqrtFuel logFuel
      lrDeterminantFixed16KLeFourRoot) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantFixed16Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point :=
  lrDeterminantFixed16KLeFourRegion_certificate_of_semanticD9Tree
    tree.toSemanticCheckedTree

end CheckedTree
end LRFiniteDeterminantRestrictedD9HybridPayloadFree
end CourtadeKumar
