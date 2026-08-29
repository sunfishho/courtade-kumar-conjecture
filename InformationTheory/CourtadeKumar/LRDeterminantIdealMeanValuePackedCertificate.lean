import InformationTheory.CourtadeKumar.LRDeterminantIdealMeanValueEvaluator

/-!
# Packed correlated-mean ideal certificates

The compact natural/mean tree uses the five-character preorder alphabet

* `N`, `M`: natural and correlated mean-value accepted leaves;
* `s`, `k`, `h`: midpoint splits in `s`, `k`, and `chi`, followed by the
  lower and then the upper subtree.

The parser is total and length-fuelled.  The public decoder accepts exactly
one complete tree, so invalid tokens, incomplete subtrees, and trailing input
are rejected.  Decoding carries no proof authority: `packedCheck` reruns the
independent Boolean checker supplied by the verified natural/mean oracle.

Checked chunks may be rooted at any exact `CertificateBox`.  Structural joins
use the same `axisCut` as the semantic tree checker, preserving every rational
midpoint without storing or trusting a second copy of the cut.
-/

namespace CourtadeKumar
namespace LRLowKIdealMeanValuePackedCertificate

open LRLowKIdealMeanValue

abbrev IdealTree := LRLowKIdealMeanValue.Tree

/-! ## Total full-input preorder decoder -/

/-- Decode the two accepted-leaf tokens. -/
def terminalOfToken : Char → Option IdealTree
  | 'N' => some (.accept .natural)
  | 'M' => some (.accept .mean)
  | _ => none

/-- Decode the three exact-midpoint split tokens. -/
def axisOfToken : Char → Option CertificateAxis
  | 's' => some .s
  | 'k' => some .k
  | 'h' => some .chi
  | _ => none

/-- Parse one preorder tree and return its unconsumed suffix.  The fuel makes
the definition total and bounds recursive nesting; it is not trusted data. -/
def parsePreorder :
    ℕ → List Char → Option (IdealTree × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, token :: rest =>
      match terminalOfToken token with
      | some tree => some (tree, rest)
      | none =>
          match axisOfToken token with
          | none => none
          | some axis =>
              match parsePreorder fuel rest with
              | none => none
              | some (lower, afterLower) =>
                  match parsePreorder fuel afterLower with
                  | none => none
                  | some (upper, afterUpper) =>
                      some (.split axis lower upper, afterUpper)

/-- Decode exactly one complete preorder character list.  One more than the
input length is strictly larger than the nesting depth of any valid tree. -/
def decodeChars (chars : List Char) : Option IdealTree :=
  match parsePreorder (chars.length + 1) chars with
  | some (tree, []) => some tree
  | _ => none

/-- Decode exactly one complete packed natural/mean topology. -/
def decode (packed : String) : Option IdealTree :=
  decodeChars packed.toList

/-- Exact success criterion at the full-input boundary. -/
theorem decodeChars_eq_some_iff (chars : List Char) (tree : IdealTree) :
    decodeChars chars = some tree ↔
      parsePreorder (chars.length + 1) chars = some (tree, []) := by
  unfold decodeChars
  generalize hparse : parsePreorder (chars.length + 1) chars = result
  cases result with
  | none => simp
  | some result =>
      rcases result with ⟨candidate, remaining⟩
      cases remaining <;> simp

/-! ## Independent replay and arbitrary-root chunks -/

/-- Decode a packed topology and run the existing independent tree checker at
the supplied exact root box. -/
def packedCheck {targets : TargetTriple}
    (oracle : AutoOracle targets) (root : CertificateBox)
    (packed : String) : Bool :=
  match decode packed with
  | none => false
  | some tree => tree.check oracle root

/-- A checked compact natural/mean tree rooted at an arbitrary exact box. -/
structure CheckedChunk {targets : TargetTriple}
    (oracle : AutoOracle targets) (root : CertificateBox) where
  certificate : IdealTree
  checked : certificate.check oracle root = true

/-- Convert a successful packed replay at an arbitrary root into a checked
chunk.  Parse failure contradicts the successful Boolean replay. -/
def checkedChunkOfPackedCheck
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox} (packed : String)
    (checked : packedCheck oracle root packed = true) :
    CheckedChunk oracle root :=
  match hdecode : decode packed with
  | none => by
      simp [packedCheck, hdecode] at checked
  | some tree =>
      { certificate := tree
        checked := by
          simpa [packedCheck, hdecode] using checked }

/-- Reusable packed data for one arbitrary-root chunk. -/
structure PackedCheckedChunk {targets : TargetTriple}
    (oracle : AutoOracle targets) (root : CertificateBox) where
  packed : String
  checked : packedCheck oracle root packed = true

namespace PackedCheckedChunk

/-- Decode and independently replay a packed chunk. -/
def toCheckedChunk
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox} (chunk : PackedCheckedChunk oracle root) :
    CheckedChunk oracle root :=
  checkedChunkOfPackedCheck chunk.packed chunk.checked

end PackedCheckedChunk

/-! ## Exact chunk roots -/

/-- Which child is followed by one step of a chunk-root path. -/
inductive Branch where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- One exact midpoint split and branch choice. -/
structure Step where
  axis : CertificateAxis
  branch : Branch
  deriving DecidableEq, Repr

abbrev Path := List Step

/-- Follow one exact midpoint step using the semantic tree's own cut. -/
def descend (box : CertificateBox) (step : Step) : CertificateBox :=
  let cut := LRLowKIdealMeanValue.axisCut box step.axis
  match step.branch with
  | .lower => box.lower step.axis cut
  | .upper => box.upper step.axis cut

/-- Reconstruct an arbitrary chunk root from its ancestor and exact path. -/
def follow : CertificateBox → Path → CertificateBox
  | box, [] => box
  | box, step :: rest => follow (descend box step) rest

/-! ## Structural joins -/

/-- The checker for a split is exactly the conjunction of its two child
checks at the semantic midpoint boxes. -/
theorem split_check_eq_true_iff
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox} {axis : CertificateAxis}
    {lower upper : IdealTree} :
    (LRLowKIdealMeanValue.Tree.split axis lower upper).check oracle root = true ↔
      lower.check oracle
          (root.lower axis (LRLowKIdealMeanValue.axisCut root axis)) = true ∧
        upper.check oracle
          (root.upper axis (LRLowKIdealMeanValue.axisCut root axis)) = true := by
  simp [LRLowKIdealMeanValue.Tree.check]

/-- Structurally join two checked children at the exact midpoint selected by
the semantic tree.  No arithmetic result is trusted or recomputed here. -/
def join
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox} (axis : CertificateAxis)
    (lower : CheckedChunk oracle
      (root.lower axis (LRLowKIdealMeanValue.axisCut root axis)))
    (upper : CheckedChunk oracle
      (root.upper axis (LRLowKIdealMeanValue.axisCut root axis))) :
    CheckedChunk oracle root where
  certificate := .split axis lower.certificate upper.certificate
  checked := (split_check_eq_true_iff).2 ⟨lower.checked, upper.checked⟩

/-- Join two chunks at the exact arithmetic `s` midpoint. -/
def joinS
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox}
    (lower : CheckedChunk oracle
      (root.lower .s (LRLowKIdealMeanValue.axisCut root .s)))
    (upper : CheckedChunk oracle
      (root.upper .s (LRLowKIdealMeanValue.axisCut root .s))) :
    CheckedChunk oracle root :=
  join .s lower upper

/-- Join two chunks at the exact arithmetic `k` midpoint. -/
def joinK
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox}
    (lower : CheckedChunk oracle
      (root.lower .k (LRLowKIdealMeanValue.axisCut root .k)))
    (upper : CheckedChunk oracle
      (root.upper .k (LRLowKIdealMeanValue.axisCut root .k))) :
    CheckedChunk oracle root :=
  join .k lower upper

/-- Join two chunks at the exact arithmetic `chi` midpoint. -/
def joinChi
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox}
    (lower : CheckedChunk oracle
      (root.lower .chi (LRLowKIdealMeanValue.axisCut root .chi)))
    (upper : CheckedChunk oracle
      (root.upper .chi (LRLowKIdealMeanValue.axisCut root .chi))) :
    CheckedChunk oracle root :=
  join .chi lower upper

namespace CheckedChunk

/-- Forget the chunk wrapper at any exact root and recover the theorem-facing
checked-tree interface. -/
def toCheckedTree
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox} (chunk : CheckedChunk oracle root) :
    LRLowKIdealMeanValue.CheckedTree oracle root where
  certificate := chunk.certificate
  checked := chunk.checked

end CheckedChunk

/-! ## Packed trees and exact low-`k` assembly -/

/-- A packed checked tree at an arbitrary exact root. -/
structure PackedCheckedTree {targets : TargetTriple}
    (oracle : AutoOracle targets) (root : CertificateBox) where
  packed : String
  checked : packedCheck oracle root packed = true

namespace PackedCheckedTree

/-- Decode and replay a packed tree at its declared exact root. -/
def toCheckedTree
    {targets : TargetTriple} {oracle : AutoOracle targets}
    {root : CertificateBox} (tree : PackedCheckedTree oracle root) :
    LRLowKIdealMeanValue.CheckedTree oracle root :=
  (checkedChunkOfPackedCheck tree.packed tree.checked).toCheckedTree

end PackedCheckedTree

/-- Two successful packed root replays discharge exactly the middle and upper
fields of the remaining low-`k` ideal certificate. -/
def lowKIdealReplayCertificate_of_packedTrees
    (middleOracle : AutoOracle middleTargets)
    (upperOracle : AutoOracle upperTargets)
    (middleTree : PackedCheckedTree middleOracle middleRoot)
    (upperTree : PackedCheckedTree upperOracle upperRoot) :
    LRLowKIdealReplayCertificate :=
  lowKIdealReplayCertificate_of_checkedTrees
    middleOracle upperOracle middleTree.toCheckedTree upperTree.toCheckedTree

/-- One successful packed replay at the exact restricted root discharges the
`1 <= k <= 4` ideal theorem used by the restricted determinant assembly.
This interface is valid for a tree whose first cut is the generic arithmetic
midpoint; the historical forest instead uses the two-component adapter below. -/
def idealOneToFour_of_packedTree
    (oracle : AutoOracle restrictedTargets)
    (tree : PackedCheckedTree oracle restrictedRoot) :
    LRDeterminantIdealOneToFourTheorem :=
  LRLowKIdealMeanValue.idealOneToFour_of_checkedTree
    oracle tree.toCheckedTree

/-- Exact packed adapter for the historical restricted forest.  Its two
components have roots `[1,2]` and `[2,4]`; the theorem-level case split fixes
the outer cut at `k=2` without overloading the arithmetic-midpoint token. -/
def idealOneToFour_of_packedForest
    (oracle : AutoOracle restrictedTargets)
    (lowerTree : PackedCheckedTree oracle restrictedLowerRoot)
    (upperTree : PackedCheckedTree oracle restrictedUpperRoot) :
    LRDeterminantIdealOneToFourTheorem :=
  LRLowKIdealMeanValue.idealOneToFour_of_twoCheckedTrees oracle
    lowerTree.toCheckedTree upperTree.toCheckedTree

/-! These definitional reductions document exact rejection behavior at the
public string boundary. -/

theorem decode_natural : decode "N" = some (.accept .natural) := by rfl
theorem decode_mean : decode "M" = some (.accept .mean) := by rfl
theorem decode_empty : decode "" = none := by rfl
theorem decode_incomplete_split : decode "k" = none := by rfl
theorem decode_incomplete_upper : decode "hN" = none := by rfl
theorem decode_trailing : decode "NM" = none := by rfl
theorem decode_invalid : decode "?" = none := by rfl

end LRLowKIdealMeanValuePackedCertificate
end CourtadeKumar
