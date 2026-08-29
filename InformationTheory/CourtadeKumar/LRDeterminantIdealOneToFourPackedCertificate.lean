import InformationTheory.CourtadeKumar.LRDeterminantIdealOneToFourHybridAutoTree

/-!
# Packed certificates for the restricted deep ideal band

The hybrid ideal tree has a five-character preorder alphabet:

* `D`, `C`: direct and coarse accepted leaves;
* `s`, `k`, `h`: binary splits in `s`, `k`, and `chi`, followed by the lower
  and then the upper subtree.

Parsing is total and fuelled by one more than the input length.  A public
decode succeeds only when one complete tree consumes the entire string, so
invalid tokens, incomplete trees, and trailing input are all rejected.

Decoded trees still have no proof authority.  `packedCheck` runs the
independent Boolean replay from the hybrid auto-tree module.  Successful
replays can be packaged either as arbitrary-root chunks for structural joins
or as the root-specific `CheckedTree` used by the ideal theorem adapter.
-/

namespace CourtadeKumar
namespace LRDeterminantIdealOneToFourPackedCertificate

abbrev IdealTree := LRDeterminantIdealOneToFourHybridAutoTree.Tree

/-! ## Total preorder decoder -/

/-- Decode the two accepted-leaf tokens. -/
def terminalOfToken : Char → Option IdealTree
  | 'D' => some (.accept .direct)
  | 'C' => some (.accept .coarse)
  | _ => none

/-- Decode the three split-axis tokens. -/
def axisOfToken : Char → Option CertificateAxis
  | 's' => some .s
  | 'k' => some .k
  | 'h' => some .chi
  | _ => none

/-- Parse one preorder tree and return its unconsumed suffix.  The fuel makes
the function total; it bounds recursive nesting, not trusted input size. -/
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

/-- Decode exactly one complete preorder character list. -/
def decodeChars (chars : List Char) : Option IdealTree :=
  match parsePreorder (chars.length + 1) chars with
  | some (tree, []) => some tree
  | _ => none

/-- Decode exactly one complete packed ideal topology. -/
def decode (packed : String) : Option IdealTree :=
  decodeChars packed.toList

/-- Exact success criterion at the complete-input boundary. -/
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

/-! ## Independent replay and packed chunks -/

/-- Decode a packed topology and run the existing independent tree checker
at the supplied exact root box. -/
def packedCheck (terms logFuel : ℕ) (margin : ℚ)
    (root : CertificateBox) (packed : String) : Bool :=
  match decode packed with
  | none => false
  | some tree => tree.check terms logFuel margin root

/-- A checked compact tree rooted at an arbitrary exact box.  This is the
structural unit used to assemble chunked replay files. -/
structure CheckedChunk
    (terms logFuel : ℕ) (margin : ℚ) (root : CertificateBox) where
  certificate : IdealTree
  checked : certificate.check terms logFuel margin root = true

/-- Convert a successful packed replay at an arbitrary root into a checked
chunk.  Parse failure contradicts the assumed successful Boolean replay. -/
def checkedChunkOfPackedCheck
    {terms logFuel : ℕ} {margin : ℚ} {root : CertificateBox}
    (packed : String)
    (checked : packedCheck terms logFuel margin root packed = true) :
    CheckedChunk terms logFuel margin root :=
  match hdecode : decode packed with
  | none => by
      simp [packedCheck, hdecode] at checked
  | some tree =>
      { certificate := tree
        checked := by
          simpa [packedCheck, hdecode] using checked }

/-- Reusable packed certificate data for one arbitrary-root chunk. -/
structure PackedCheckedChunk
    (terms logFuel : ℕ) (margin : ℚ) (root : CertificateBox) where
  packed : String
  checked : packedCheck terms logFuel margin root packed = true

namespace PackedCheckedChunk

/-- Decode and independently replay a packed chunk. -/
def toCheckedChunk
    {terms logFuel : ℕ} {margin : ℚ} {root : CertificateBox}
    (chunk : PackedCheckedChunk terms logFuel margin root) :
    CheckedChunk terms logFuel margin root :=
  checkedChunkOfPackedCheck chunk.packed chunk.checked

end PackedCheckedChunk

/-! ## Exact chunk roots and structural joins -/

/-- Which child is followed by one step of a chunk-root path. -/
inductive Branch where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- One ideal-tree split and branch choice. -/
structure Step where
  axis : CertificateAxis
  branch : Branch
  deriving DecidableEq, Repr

abbrev Path := List Step

/-- Follow one exact ideal-tree split.  In particular, a `k` step uses the
hybrid module's logarithmic cut, while a `chi` step uses its ordinary exact
arithmetic midpoint. -/
def descend (box : CertificateBox) (step : Step) : CertificateBox :=
  let cut := LRDeterminantIdealOneToFourHybridAutoTree.axisCut box step.axis
  match step.branch with
  | .lower => box.lower step.axis cut
  | .upper => box.upper step.axis cut

/-- Reconstruct a chunk root from an ancestor box and an exact split path. -/
def follow : CertificateBox → Path → CertificateBox
  | box, [] => box
  | box, step :: rest => follow (descend box step) rest

/-- Structurally join two checked children at the exact cut selected by the
hybrid ideal tree.  No arithmetic result is trusted or recomputed at the
join. -/
def join
    {terms logFuel : ℕ} {margin : ℚ} {root : CertificateBox}
    (axis : CertificateAxis)
    (lower : CheckedChunk terms logFuel margin
      (root.lower axis
        (LRDeterminantIdealOneToFourHybridAutoTree.axisCut root axis)))
    (upper : CheckedChunk terms logFuel margin
      (root.upper axis
        (LRDeterminantIdealOneToFourHybridAutoTree.axisCut root axis))) :
    CheckedChunk terms logFuel margin root where
  certificate := .split axis lower.certificate upper.certificate
  checked := by
    simp only [
      LRDeterminantIdealOneToFourHybridAutoTree.Tree.check,
      Bool.and_eq_true]
    exact ⟨lower.checked, upper.checked⟩

/-- Join two chunks at the exact logarithmic-`k` cut. -/
def joinK
    {terms logFuel : ℕ} {margin : ℚ} {root : CertificateBox}
    (lower : CheckedChunk terms logFuel margin
      (root.lower .k
        (LRDeterminantIdealOneToFourHybridAutoTree.logarithmicKCut root)))
    (upper : CheckedChunk terms logFuel margin
      (root.upper .k
        (LRDeterminantIdealOneToFourHybridAutoTree.logarithmicKCut root))) :
    CheckedChunk terms logFuel margin root :=
  join .k lower upper

/-- Join two chunks at the ordinary exact arithmetic `chi` midpoint. -/
def joinChi
    {terms logFuel : ℕ} {margin : ℚ} {root : CertificateBox}
    (lower : CheckedChunk terms logFuel margin
      (root.lower .chi (RationalEnclosure.center root.chiInterval)))
    (upper : CheckedChunk terms logFuel margin
      (root.upper .chi (RationalEnclosure.center root.chiInterval))) :
    CheckedChunk terms logFuel margin root :=
  join .chi lower upper

namespace CheckedChunk

/-- Convert a completely joined root chunk to the existing theorem-facing
checked-tree interface. -/
def toCheckedTree
    {terms logFuel : ℕ} {margin : ℚ}
    (chunk : CheckedChunk terms logFuel margin
      LRDeterminantIdealOneToFourHybridAutoTree.rootBox) :
    LRDeterminantIdealOneToFourHybridAutoTree.CheckedTree
      terms logFuel margin where
  certificate := chunk.certificate
  checked := chunk.checked

end CheckedChunk

/-! ## Root-specific packed certificates -/

/-- A packed replay at the exact `[1,4] × [0,1]` ideal root. -/
structure PackedCheckedTree (terms logFuel : ℕ) (margin : ℚ) where
  packed : String
  checked : packedCheck terms logFuel margin
    LRDeterminantIdealOneToFourHybridAutoTree.rootBox packed = true

namespace PackedCheckedTree

/-- Decode and replay a root-specific packed certificate. -/
def toCheckedTree
    {terms logFuel : ℕ} {margin : ℚ}
    (tree : PackedCheckedTree terms logFuel margin) :
    LRDeterminantIdealOneToFourHybridAutoTree.CheckedTree
      terms logFuel margin :=
  (checkedChunkOfPackedCheck tree.packed tree.checked).toCheckedTree

/-- Supply the exact restricted ideal theorem from a successful packed
root replay at margin `3/5`. -/
def toIdealOneToFour
    {terms logFuel : ℕ} {margin : ℚ}
    (hmargin : margin = 3 / 5)
    (tree : PackedCheckedTree terms logFuel margin) :
    LRDeterminantIdealOneToFourTheorem :=
  LRDeterminantIdealOneToFourHybridAutoTree.idealOneToFour_of_checkedTree
    hmargin tree.toCheckedTree

end PackedCheckedTree

/-! These definitional reductions document exact rejection behavior at the
public string boundary. -/

theorem decode_empty : decode "" = none := by rfl
theorem decode_incomplete_split : decode "k" = none := by rfl
theorem decode_incomplete_upper : decode "hD" = none := by rfl
theorem decode_trailing : decode "DC" = none := by rfl
theorem decode_invalid : decode "?" = none := by rfl

end LRDeterminantIdealOneToFourPackedCertificate
end CourtadeKumar
