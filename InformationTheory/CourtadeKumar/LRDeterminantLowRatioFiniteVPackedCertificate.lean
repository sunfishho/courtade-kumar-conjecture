import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVAutoTree
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVFirstBracketAutoTree

/-!
# Packed finite-`V` subdivision certificates

Generated finite low-ratio trees can have many leaves even though every
terminal datum and split axis belongs to a tiny finite alphabet.  This module
stores such a topology as an ASCII preorder string and reconstructs the
existing compact tree before running its ordinary Boolean checker.

The direct-`V` alphabet is

* `N`, `M`: natural and mean-value accepted leaves;
* `J`: a nonpositive-`J` discard;
* `E`, `X`, `V`: the three physical discard reasons;
* `s`, `k`, `h`: binary midpoint splits, followed by the lower and then the
  upper subtree.

The first-bracket alphabet is the subset `N`, `M`, `s`, `k`, `h`.  Parsing is
total and fuelled by one more than the input length.  A packed certificate is
accepted only when one complete tree consumes the entire string: invalid
tokens, incomplete subtrees, and trailing tokens all return `none`.

The decoder and all packaging proofs are ordinary kernel-reducible Lean
definitions.  In particular, no compiler-backed decision procedure,
non-kernel definition, or external certificate authority is used.
-/

namespace CourtadeKumar
namespace LRDeterminantLowRatioFiniteVPackedCertificate

/-! ## Shared exact preorder parser -/

/-- Decode the three lowercase split tokens. -/
def axisOfToken : Char → Option CertificateAxis
  | 's' => some .s
  | 'k' => some .k
  | 'h' => some .chi
  | _ => none

/-- A total preorder parser.  `terminal` recognizes the leaf alphabet and
`splitNode` builds an internal node after recursively parsing its lower and
upper children.  The unconsumed suffix is returned explicitly. -/
def parsePreorder {Tree : Type}
    (terminal : Char → Option Tree)
    (splitNode : CertificateAxis → Tree → Tree → Tree) :
    ℕ → List Char → Option (Tree × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, token :: rest =>
      match terminal token with
      | some tree => some (tree, rest)
      | none =>
          match axisOfToken token with
          | none => none
          | some axis =>
              match parsePreorder terminal splitNode fuel rest with
              | none => none
              | some (lower, afterLower) =>
                  match parsePreorder terminal splitNode fuel afterLower with
                  | none => none
                  | some (upper, afterUpper) =>
                      some (splitNode axis lower upper, afterUpper)

/-- Decode exactly one complete tree.  The length-derived fuel is larger than
every possible nesting depth in a nonempty preorder string, while the final
empty-suffix pattern rejects all trailing input. -/
def decodePreorder {Tree : Type}
    (terminal : Char → Option Tree)
    (splitNode : CertificateAxis → Tree → Tree → Tree)
    (chars : List Char) : Option Tree :=
  match parsePreorder terminal splitNode (chars.length + 1) chars with
  | some (tree, []) => some tree
  | _ => none

/-- Exact success criterion for the complete decoder. -/
theorem decodePreorder_eq_some_iff {Tree : Type}
    (terminal : Char → Option Tree)
    (splitNode : CertificateAxis → Tree → Tree → Tree)
    (chars : List Char) (tree : Tree) :
    decodePreorder terminal splitNode chars = some tree ↔
      parsePreorder terminal splitNode (chars.length + 1) chars =
        some (tree, []) := by
  unfold decodePreorder
  generalize hparse :
    parsePreorder terminal splitNode (chars.length + 1) chars = result
  cases result with
  | none => simp
  | some result =>
      rcases result with ⟨candidate, remaining⟩
      cases remaining <;> simp

/-! ## Exact midpoint paths for chunk roots -/

/-- Which child of a midpoint split is followed by a chunk path. -/
inductive Branch where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- One axis-and-side step in a midpoint path.  No rational cut is stored. -/
structure MidpointStep where
  axis : CertificateAxis
  branch : Branch
  deriving DecidableEq, Repr

abbrev MidpointPath := List MidpointStep

/-- The common exact midpoint cut used by both compact tree implementations. -/
def midpointCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

/-- Follow one midpoint step from a box. -/
def descend (box : CertificateBox) (step : MidpointStep) : CertificateBox :=
  let cut := midpointCut box step.axis
  match step.branch with
  | .lower => box.lower step.axis cut
  | .upper => box.upper step.axis cut

/-- Reconstruct a chunk root solely from its root box and midpoint path. -/
def follow : CertificateBox → MidpointPath → CertificateBox
  | box, [] => box
  | box, step :: rest => follow (descend box step) rest

/-- The shared midpoint agrees definitionally, axis by axis, with the direct
compact-tree midpoint. -/
theorem midpointCut_eq_directAxisCut
    (box : CertificateBox) (axis : CertificateAxis) :
    midpointCut box axis = LRLowRatioFiniteVAutoTree.axisCut box axis := by
  cases axis <;> rfl

/-- The shared midpoint also agrees with the first-bracket compact tree. -/
theorem midpointCut_eq_firstBracketAxisCut
    (box : CertificateBox) (axis : CertificateAxis) :
    midpointCut box axis =
      LRDeterminantLowRatioFiniteVFirstBracketAutoTree.axisCut box axis := by
  cases axis <;> rfl

/-! ## Packed direct-`V` trees -/

namespace Direct

/-- Decode a direct-`V` terminal token. -/
def terminalOfToken : Char → Option LRLowRatioFiniteVAutoTree.Tree
  | 'N' => some (.accept .natural)
  | 'M' => some (.accept .meanValue)
  | 'J' => some (.discard .jNonpositive)
  | 'E' => some (.discard (.physical .eAtLeastOne))
  | 'X' => some (.discard (.physical .xBelowHighShape))
  | 'V' => some (.discard (.physical .vBelowThird))
  | _ => none

/-- Decode a complete direct-`V` preorder character list. -/
def decodeChars (chars : List Char) :
    Option LRLowRatioFiniteVAutoTree.Tree :=
  decodePreorder terminalOfToken LRLowRatioFiniteVAutoTree.Tree.split chars

/-- Decode a complete packed direct-`V` topology. -/
def decode (packed : String) : Option LRLowRatioFiniteVAutoTree.Tree :=
  decodeChars packed.toList

/-- Decode and run the established compact direct-`V` checker. -/
def packedCheck (terms sqrtFuel logFuel : ℕ)
    (root : CertificateBox) (packed : String) : Bool :=
  match decode packed with
  | none => false
  | some tree => tree.check terms sqrtFuel logFuel root

/-- Package a successful packed replay in the existing compact checked-tree
interface.  The impossible parse-failure branch follows directly from the
assumed Boolean equality. -/
def autoTaggedCheckedTreeOfPackedCheck
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (packed : String)
    (checked : packedCheck terms sqrtFuel logFuel root packed = true) :
    LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel root :=
  match hdecode : decode packed with
  | none => by
      simp [packedCheck, hdecode] at checked
  | some tree =>
      { certificate := tree
        checked := by
          simpa [packedCheck, hdecode] using checked }

/-- A reusable packed direct-`V` certificate.  Generated source files need
store only the ASCII string and an ordinary proof, usually `by rfl`, of its
kernel-reducible replay. -/
structure PackedCheckedTree
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  packed : String
  checked : packedCheck terms sqrtFuel logFuel root packed = true

namespace PackedCheckedTree

/-- Convert a packed checked tree to the existing compact boundary. -/
def toAutoTaggedCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : PackedCheckedTree terms sqrtFuel logFuel root) :
    LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel root :=
  autoTaggedCheckedTreeOfPackedCheck tree.packed tree.checked

/-- Convert all the way to the semantic direct-`V` checked tree. -/
def toCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : PackedCheckedTree terms sqrtFuel logFuel root) :
    LRLowRatioFiniteVMeanValue.CheckedTree
      (LRLowRatioFiniteVConcreteOracle.concreteOracle terms) root :=
  (toAutoTaggedCheckedTree tree).toCheckedTree

end PackedCheckedTree

/-- Structurally join two already checked midpoint chunks.  This lets a
large generated replay remain split across source modules without repeating
or trusting any arithmetic result at the join. -/
def join
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (axis : CertificateAxis)
    (lower : LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel
      (root.lower axis (LRLowRatioFiniteVAutoTree.axisCut root axis)))
    (upper : LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel
      (root.upper axis (LRLowRatioFiniteVAutoTree.axisCut root axis))) :
    LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel root where
  certificate := .split axis lower.certificate upper.certificate
  checked := by
    simp only [LRLowRatioFiniteVAutoTree.Tree.check, Bool.and_eq_true]
    exact ⟨lower.checked, upper.checked⟩

/-! The following reductions document exact rejection at the public string
boundary.  They are ordinary definitional proofs, not decision procedures. -/

theorem decode_empty : decode "" = none := by rfl
theorem decode_incomplete_split : decode "s" = none := by rfl
theorem decode_incomplete_upper : decode "sN" = none := by rfl
theorem decode_trailing : decode "NN" = none := by rfl
theorem decode_invalid : decode "?" = none := by rfl

end Direct

/-! ## Packed first-bracket trees -/

namespace FirstBracket

/-- Decode a first-bracket terminal token.  Discard tokens are deliberately
absent from this alphabet. -/
def terminalOfToken : Char → Option
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.Tree
  | 'N' => some (.accept .natural)
  | 'M' => some (.accept .meanValue)
  | _ => none

/-- Decode a complete first-bracket preorder character list. -/
def decodeChars (chars : List Char) : Option
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.Tree :=
  decodePreorder terminalOfToken
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.Tree.split chars

/-- Decode a complete packed first-bracket midpoint topology. -/
def decode (packed : String) : Option
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.Tree :=
  decodeChars packed.toList

/-- Decode and run the established compact first-bracket checker. -/
def packedCheck (terms sqrtFuel logFuel : ℕ)
    (root : CertificateBox) (packed : String) : Bool :=
  match decode packed with
  | none => false
  | some tree => tree.check terms sqrtFuel logFuel root

/-- Package a successful packed replay in the existing compact first-bracket
checked-tree interface. -/
def autoTaggedCheckedTreeOfPackedCheck
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (packed : String)
    (checked : packedCheck terms sqrtFuel logFuel root packed = true) :
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel root :=
  match hdecode : decode packed with
  | none => by
      simp [packedCheck, hdecode] at checked
  | some tree =>
      { certificate := tree
        checked := by
          simpa [packedCheck, hdecode] using checked }

/-- A reusable packed first-bracket certificate for one midpoint-rooted
tree, in particular for one of the ten fixed historical slabs. -/
structure PackedCheckedTree
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  packed : String
  checked : packedCheck terms sqrtFuel logFuel root packed = true

namespace PackedCheckedTree

/-- Convert a packed first-bracket tree to the existing compact boundary. -/
def toAutoTaggedCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : PackedCheckedTree terms sqrtFuel logFuel root) :
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel root :=
  autoTaggedCheckedTreeOfPackedCheck tree.packed tree.checked

/-- Convert one packed slab directly to its semantic first-bracket tree. -/
def toFirstBracketTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : PackedCheckedTree terms sqrtFuel logFuel root) :
    LRLowRatioFiniteVMeanValue.FirstBracketTree root :=
  (toAutoTaggedCheckedTree tree).toFirstBracketTree

end PackedCheckedTree

/-- Structurally join two checked midpoint chunks within a fixed slab. -/
def join
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (axis : CertificateAxis)
    (lower :
      LRDeterminantLowRatioFiniteVFirstBracketAutoTree.AutoTaggedCheckedTree
        terms sqrtFuel logFuel
        (root.lower axis
          (LRDeterminantLowRatioFiniteVFirstBracketAutoTree.axisCut
            root axis)))
    (upper :
      LRDeterminantLowRatioFiniteVFirstBracketAutoTree.AutoTaggedCheckedTree
        terms sqrtFuel logFuel
        (root.upper axis
          (LRDeterminantLowRatioFiniteVFirstBracketAutoTree.axisCut
            root axis))) :
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.AutoTaggedCheckedTree
      terms sqrtFuel logFuel root where
  certificate := .split axis lower.certificate upper.certificate
  checked := by
    simp only [
      LRDeterminantLowRatioFiniteVFirstBracketAutoTree.Tree.check,
      Bool.and_eq_true]
    exact ⟨lower.checked, upper.checked⟩

/-! ## Ten independent packed dyadic slabs -/

/-- The nine outer first-bracket cuts are explicit historical dyadics, not
midpoints of the aggregate root.  Accordingly, a forest stores ten separate
packed midpoint trees at the exact slab roots and delegates the outer joins
to the already proved fixed-cut adapter. -/
structure PackedTenSlabForest
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  slab0 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab0Root root)
  slab1 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab1Root root)
  slab2 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab2Root root)
  slab3 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab3Root root)
  slab4 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab4Root root)
  slab5 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab5Root root)
  slab6 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab6Root root)
  slab7 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab7Root root)
  slab8 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab8Root root)
  slab9 : PackedCheckedTree terms sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.FirstBracketForest.firstBracketSlab9Root root)

namespace PackedTenSlabForest

/-- Convert all ten packed slab replays to the existing fixed-cut forest. -/
def toTenSlabForest
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : PackedTenSlabForest terms sqrtFuel logFuel root) :
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.TenSlabForest
      terms sqrtFuel logFuel root where
  slab0 := forest.slab0.toAutoTaggedCheckedTree
  slab1 := forest.slab1.toAutoTaggedCheckedTree
  slab2 := forest.slab2.toAutoTaggedCheckedTree
  slab3 := forest.slab3.toAutoTaggedCheckedTree
  slab4 := forest.slab4.toAutoTaggedCheckedTree
  slab5 := forest.slab5.toAutoTaggedCheckedTree
  slab6 := forest.slab6.toAutoTaggedCheckedTree
  slab7 := forest.slab7.toAutoTaggedCheckedTree
  slab8 := forest.slab8.toAutoTaggedCheckedTree
  slab9 := forest.slab9.toAutoTaggedCheckedTree

/-- Convert the ten packed slabs to the aggregate semantic first bracket. -/
def toFirstBracketTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : PackedTenSlabForest terms sqrtFuel logFuel root) :
    LRLowRatioFiniteVMeanValue.FirstBracketTree root :=
  (toTenSlabForest forest).toFirstBracketTree

end PackedTenSlabForest

theorem decode_empty : decode "" = none := by rfl
theorem decode_incomplete_split : decode "h" = none := by rfl
theorem decode_incomplete_upper : decode "hM" = none := by rfl
theorem decode_trailing : decode "MM" = none := by rfl
theorem decode_invalid_discard : decode "J" = none := by rfl

end FirstBracket

end LRDeterminantLowRatioFiniteVPackedCertificate
end CourtadeKumar
