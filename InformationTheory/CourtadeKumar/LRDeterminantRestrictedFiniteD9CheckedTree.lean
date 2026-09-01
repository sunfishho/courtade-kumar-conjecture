import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteD9

/-!
# Restricted checked trees for the finite-D9 determinant target

The final `K \le 4` determinant ledger uses the finite-D9 replay only at
points satisfying `s < k`.  This module records that hypothesis in the
checked-tree semantics rather than asking a generated tree to prove the D9
target on the unused wedge `k \le s`.

The payload-free accepted-leaf evaluator and the established physical/
nonpositive-`J` discard evaluator are reused unchanged.  The restricted
discard checker additionally accepts a box when the exact rational bounds
satisfy `box.kHi \le box.sLo`; every point of such a box has `k \le s`, so it
cannot satisfy the restricted relevance predicate.

Generated arithmetic can be checked one terminal at a time with `ofAccept`
and `ofDiscard`.  `join` then assembles those proof objects without replaying
any leaf arithmetic.
-/

set_option autoImplicit false

namespace CourtadeKumar

/-- Relevance for the finite-D9 rows of the restricted determinant ledger. -/
def LRFiniteDeterminantRestrictedD9Relevant
    (point : CertificatePoint) : Prop :=
  LRHighShapeVRelevant point ∧ point.s < point.k

/-- A discard checker is compatible with the restricted finite-D9 domain
when every accepted discard excludes either high-shape relevance or `s < k`.
-/
def LRFiniteDeterminantRestrictedRawDiscardCompatible
    {DiscardData : Type}
    (discardCheck : CertificateBox → DiscardData → Bool) : Prop :=
  ∀ box data, discardCheck box data = true →
    ∀ point, box.Contains point →
      ¬ LRFiniteDeterminantRestrictedD9Relevant point

/-- Abstract kernel-checked tree for the exact D9 target on the restricted
domain `LRHighShapeVRelevant point ∧ point.s < point.k`. -/
structure LRFiniteDeterminantRestrictedRawD9CheckedTree
    (root : CertificateBox) where
  AcceptData : Type
  DiscardData : Type
  payloadCheck : CertificateBox → AcceptData → Bool
  enclose : CertificateBox → AcceptData → RationalEnclosure
  discardCheck : CertificateBox → DiscardData → Bool
  encloseSound : CheckedEnclosureLeafEvaluatorSound
    lrFiniteDeterminantD9ReplayTarget payloadCheck enclose
  discardCompatible :
    LRFiniteDeterminantRestrictedRawDiscardCompatible discardCheck
  certificate : SubdivisionCertificate AcceptData DiscardData
  checked : certificate.check
    (checkedEnclosureLeafAccepts payloadCheck enclose)
    discardCheck root = true

namespace LRFiniteDeterminantRestrictedRawD9CheckedTree

/-- Semantic consequence of a checked tree on the restricted domain. -/
theorem target_nonnegative
    {root : CertificateBox}
    (tree : LRFiniteDeterminantRestrictedRawD9CheckedTree root)
    {point : CertificatePoint}
    (hpoint : root.Contains point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsk : point.s < point.k) :
    0 ≤ lrFiniteDeterminantD9ReplayTarget point := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    (Relevant := LRFiniteDeterminantRestrictedD9Relevant)
    tree.encloseSound tree.discardCompatible tree.checked
    point hpoint ⟨hrelevant, hsk⟩

end LRFiniteDeterminantRestrictedRawD9CheckedTree

/-- A restricted raw D9 tree on any root containing the ledger row supplies
the exact `s < k ≤ 4` row interface. -/
theorem lrDeterminantKLeFourRegionCertificate_of_restrictedRawD9Tree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        point.s < point.k → point.k ≤ 4 → root.Contains point)
    (tree : LRFiniteDeterminantRestrictedRawD9CheckedTree root) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point := by
  intro point hinterior hrelevant hregion hsk hkFour
  exact lrDeterminantAdmittedTarget_of_D9ReplayTarget hinterior
    (tree.target_nonnegative
      (root_contains hinterior hregion hsk hkFour) hrelevant hsk)

/-- A restricted checked topology on the clipped fixed-16 root closes its
field of the restricted determinant ledger. -/
theorem lrDeterminantFixed16KLeFourRegion_certificate_of_restrictedD9Tree
    (tree : LRFiniteDeterminantRestrictedRawD9CheckedTree
      lrDeterminantFixed16KLeFourRoot) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantFixed16Region point →
      point.s < point.k →
      point.k ≤ 4 →
      LRDeterminantAdmittedTarget point :=
  lrDeterminantKLeFourRegionCertificate_of_restrictedRawD9Tree
    lrDeterminantFixed16KLeFourRoot_contains tree

namespace LRFiniteDeterminantRestrictedD9PayloadFree

abbrev Tree := LRFiniteDeterminantD9PayloadFree.Tree

/-- Exact rational test certifying that every point of `box` has `k ≤ s`. -/
def geometricDiscardCheck (box : CertificateBox) : Bool :=
  decide (box.kHi ≤ box.sLo)

theorem geometricDiscardCheck_sound
    (box : CertificateBox)
    (hcheck : geometricDiscardCheck box = true) :
    ∀ point, box.Contains point →
      ¬ LRFiniteDeterminantRestrictedD9Relevant point := by
  have hbounds : box.kHi ≤ box.sLo := by
    simpa only [geometricDiscardCheck, decide_eq_true_eq] using hcheck
  have hboundsReal : (box.kHi : ℝ) ≤ (box.sLo : ℝ) := by
    exact_mod_cast hbounds
  intro point hpoint hrelevant
  have hks : point.k ≤ point.s :=
    hpoint.2.2.2.1.trans (hboundsReal.trans hpoint.1)
  exact (not_lt_of_ge hks) hrelevant.2

/-- Restricted discard checker: first remove the whole `k ≤ s` wedge, then
fall back to the established physical/nonpositive-`J` checker. -/
def discardCheck (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (data : Unit) : Bool :=
  geometricDiscardCheck box ||
    LRFiniteDeterminantD9PayloadFree.discardCheck
      terms sqrtFuel logFuel box data

theorem discardCheck_sound (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (data : Unit)
    (hcheck : discardCheck terms sqrtFuel logFuel box data = true) :
    ∀ point, box.Contains point →
      ¬ LRFiniteDeterminantRestrictedD9Relevant point := by
  have hparts : geometricDiscardCheck box = true ∨
      LRFiniteDeterminantD9PayloadFree.discardCheck
        terms sqrtFuel logFuel box data = true := by
    simpa only [discardCheck, Bool.or_eq_true] using hcheck
  rcases hparts with hgeometric | hphysical
  · exact geometricDiscardCheck_sound box hgeometric
  · intro point hpoint hrelevant
    exact LRFiniteDeterminantD9PayloadFree.discardCheck_sound
      terms sqrtFuel logFuel box data hphysical point hpoint hrelevant.1

/-- Package a payload-free topology checked with the restricted discard
semantics as an abstract restricted raw tree. -/
def toRawCheckedTree (terms sqrtFuel logFuel : Nat)
    {root : CertificateBox} (tree : Tree)
    (hcheck : tree.check
      (LRFiniteDeterminantD9PayloadFree.accepts terms sqrtFuel logFuel)
      (discardCheck terms sqrtFuel logFuel) root = true) :
    LRFiniteDeterminantRestrictedRawD9CheckedTree root where
  AcceptData := Unit
  DiscardData := Unit
  payloadCheck :=
    LRFiniteDeterminantD9PayloadFree.payloadCheck terms sqrtFuel logFuel
  enclose := LRFiniteDeterminantD9PayloadFree.enclose terms sqrtFuel logFuel
  discardCheck := discardCheck terms sqrtFuel logFuel
  encloseSound :=
    LRFiniteDeterminantD9PayloadFree.evaluatorSound terms sqrtFuel logFuel
  discardCompatible := discardCheck_sound terms sqrtFuel logFuel
  certificate := tree
  checked := hcheck

/-- A generic payload-free topology together with its already established
restricted Boolean traversal.  This is the recoverable assembly object used
by generated terminal and structural modules. -/
structure CheckedTree
    (terms sqrtFuel logFuel : Nat) (root : CertificateBox) : Type where
  certificate : Tree
  checked : certificate.check
    (LRFiniteDeterminantD9PayloadFree.accepts terms sqrtFuel logFuel)
    (discardCheck terms sqrtFuel logFuel) root = true

/-- Synonym emphasizing the independently compiled chunk use. -/
abbrev CheckedChunk := CheckedTree

namespace CheckedTree

/-- Package one independently kernel-checked accepted leaf. -/
def ofAccept
    (terms sqrtFuel logFuel : Nat) {root : CertificateBox}
    (hcheck : LRFiniteDeterminantD9PayloadFree.accepts
      terms sqrtFuel logFuel root () = true) :
    CheckedTree terms sqrtFuel logFuel root where
  certificate := .accept ()
  checked := hcheck

/-- Package one independently kernel-checked restricted discard leaf. -/
def ofDiscard
    (terms sqrtFuel logFuel : Nat) {root : CertificateBox}
    (hcheck : discardCheck terms sqrtFuel logFuel root () = true) :
    CheckedTree terms sqrtFuel logFuel root where
  certificate := .discard ()
  checked := hcheck

/-- Join two independently checked children without replaying leaf
arithmetic. -/
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

/-- Literal-box structural join for generated modules.  The two equality
arguments bind external box literals to the children reconstructed from the
parent and split, without replaying terminal arithmetic. -/
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

/-- Forget the recoverable assembly wrapper and expose the abstract semantic
tree. -/
def toRawCheckedTree
    {terms sqrtFuel logFuel : Nat} {root : CertificateBox}
    (tree : CheckedTree terms sqrtFuel logFuel root) :
    LRFiniteDeterminantRestrictedRawD9CheckedTree root :=
  LRFiniteDeterminantRestrictedD9PayloadFree.toRawCheckedTree
    terms sqrtFuel logFuel tree.certificate tree.checked

/-- Semantic consequence of an assembled restricted payload-free tree. -/
theorem target_nonnegative
    {terms sqrtFuel logFuel : Nat} {root : CertificateBox}
    (tree : CheckedTree terms sqrtFuel logFuel root)
    {point : CertificatePoint}
    (hpoint : root.Contains point)
    (hrelevant : LRHighShapeVRelevant point)
    (hsk : point.s < point.k) :
    0 ≤ lrFiniteDeterminantD9ReplayTarget point :=
  tree.toRawCheckedTree.target_nonnegative hpoint hrelevant hsk

/-- Fixed-16 restricted-ledger theorem exported by a fully assembled
payload-free checked tree. -/
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
  lrDeterminantFixed16KLeFourRegion_certificate_of_restrictedD9Tree
    tree.toRawCheckedTree

end CheckedTree

end LRFiniteDeterminantRestrictedD9PayloadFree
end CourtadeKumar
