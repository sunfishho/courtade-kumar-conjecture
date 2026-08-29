import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalAutoTree

/-!
# Packed certificates for the historical upper-`K` midpoint replay

The complete alphabet is deliberately tiny:

* `M` is the unique `Unit` mean-value leaf;
* `s`, `k`, and `h` are binary midpoint splits, followed in preorder by the
  lower subtree and then the upper subtree.

Parsing is total and length-fuelled.  The public decoder accepts exactly one
complete tree, so invalid tokens, incomplete trees, and trailing input are
all rejected.  Decoding itself proves nothing: `packedCheck` reruns the
concrete historical checker at every reconstructed leaf.

Arbitrary-root checked chunks and exact root paths let generated replay data
remain split across many small source modules.  The structural joins below
combine already checked children without repeating their internal arithmetic.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalPackedCertificate

namespace Auto

abbrev Tree := LRUpperKHistoricalAutoTree.Tree
abbrev CheckedTree := LRUpperKHistoricalAutoTree.CheckedTree
abbrev CheckedChunk := LRUpperKHistoricalAutoTree.CheckedChunk
abbrev Branch := LRUpperKHistoricalAutoTree.Branch
abbrev Step := LRUpperKHistoricalAutoTree.Step
abbrev Path := LRUpperKHistoricalAutoTree.Path
abbrev axisCut := LRUpperKHistoricalAutoTree.axisCut
abbrev descend := LRUpperKHistoricalAutoTree.descend
abbrev follow := LRUpperKHistoricalAutoTree.follow
abbrev oneToTwoRoot := LRUpperKHistoricalAutoTree.oneToTwoRoot
abbrev twoToFourRoot := LRUpperKHistoricalAutoTree.twoToFourRoot

end Auto

abbrev HistoricalTree := Auto.Tree

/-! ## Total full-input preorder decoder -/

/-- Decode the unique accepted-leaf token. -/
def terminalOfToken : Char → Option HistoricalTree
  | 'M' => some (.accept ())
  | _ => none

/-- Decode the three exact-midpoint split tokens. -/
def axisOfToken : Char → Option CertificateAxis
  | 's' => some .s
  | 'k' => some .k
  | 'h' => some .chi
  | _ => none

/-- Parse one preorder tree and return its unconsumed suffix.  Fuel makes the
definition total; it is derived from the input length at the public boundary. -/
def parsePreorder :
    ℕ → List Char → Option (HistoricalTree × List Char)
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

/-- Decode exactly one complete preorder character list.  The extra unit of
fuel exceeds the nesting depth of every valid nonempty input. -/
def decodeChars (chars : List Char) : Option HistoricalTree :=
  match parsePreorder (chars.length + 1) chars with
  | some (tree, []) => some tree
  | _ => none

/-- Decode exactly one complete packed historical topology. -/
def decode (packed : String) : Option HistoricalTree :=
  decodeChars packed.toList

/-- Exact success criterion at the full-input boundary. -/
theorem decodeChars_eq_some_iff (chars : List Char)
    (tree : HistoricalTree) :
    decodeChars chars = some tree ↔
      parsePreorder (chars.length + 1) chars = some (tree, []) := by
  unfold decodeChars
  generalize hparse : parsePreorder (chars.length + 1) chars = result
  cases result with
  | none => simp
  | some result =>
      rcases result with ⟨candidate, remaining⟩
      cases remaining <;> simp

/-! ## Independent packed replay and checked chunks -/

/-- Decode a packed topology and run the concrete checker from the supplied
exact root box. -/
def packedCheck (terms : ℕ) (root : CertificateBox)
    (packed : String) : Bool :=
  match decode packed with
  | none => false
  | some tree => tree.check terms root

/-- Convert a successful packed replay at an arbitrary root into the semantic
checked-chunk interface.  Parse failure contradicts the successful Boolean. -/
def checkedChunkOfPackedCheck
    {terms : ℕ} {root : CertificateBox} (packed : String)
    (checked : packedCheck terms root packed = true) :
    Auto.CheckedChunk terms root :=
  match hdecode : decode packed with
  | none => by
      simp [packedCheck, hdecode] at checked
  | some tree =>
      { certificate := tree
        checked := by
          simpa [packedCheck, hdecode] using checked }

/-- Reusable packed data for one independently checked arbitrary-root chunk. -/
structure PackedCheckedChunk (terms : ℕ) (root : CertificateBox) where
  packed : String
  checked : packedCheck terms root packed = true

namespace PackedCheckedChunk

/-- Decode and independently replay one packed chunk. -/
def toCheckedChunk
    {terms : ℕ} {root : CertificateBox}
    (chunk : PackedCheckedChunk terms root) :
    Auto.CheckedChunk terms root :=
  checkedChunkOfPackedCheck chunk.packed chunk.checked

end PackedCheckedChunk

/-! ## Exact chunk paths and root adapters -/

abbrev Branch := Auto.Branch
abbrev Step := Auto.Step
abbrev Path := Auto.Path

abbrev descend := Auto.descend
abbrev follow := Auto.follow

/-- Following a concatenated path is the same as rebasing the suffix at the
box reached by the prefix. -/
theorem follow_append (root : CertificateBox) (prefixPath suffix : Path) :
    follow root (prefixPath ++ suffix) =
      follow (follow root prefixPath) suffix := by
  induction prefixPath generalizing root with
  | nil => rfl
  | cons step rest ih =>
      simpa [follow, Auto.follow] using ih (descend root step)

/-- Singleton specialization used at each generated internal node. -/
theorem follow_append_singleton
    (root : CertificateBox) (path : Path) (step : Step) :
    follow root (path ++ [step]) = descend (follow root path) step := by
  simpa [follow, Auto.follow] using follow_append root path [step]

def lowerStep (axis : CertificateAxis) : Step :=
  { axis := axis, branch := .lower }

def upperStep (axis : CertificateAxis) : Step :=
  { axis := axis, branch := .upper }

/-- The path obtained by appending one lower step reaches exactly the lower
midpoint child of the current path root. -/
theorem follow_append_lower (root : CertificateBox) (path : Path)
    (axis : CertificateAxis) :
    follow root (path ++ [lowerStep axis]) =
      (follow root path).lower axis (Auto.axisCut (follow root path) axis) := by
  simpa [follow_append_singleton, descend, Auto.descend,
    LRUpperKHistoricalAutoTree.descend, Auto.axisCut,
    LRUpperKHistoricalAutoTree.axisCut, lowerStep]

/-- The analogous exact identity for one appended upper step. -/
theorem follow_append_upper (root : CertificateBox) (path : Path)
    (axis : CertificateAxis) :
    follow root (path ++ [upperStep axis]) =
      (follow root path).upper axis (Auto.axisCut (follow root path) axis) := by
  simpa [follow_append_singleton, descend, Auto.descend,
    LRUpperKHistoricalAutoTree.descend, Auto.axisCut,
    LRUpperKHistoricalAutoTree.axisCut, upperStep]

/-- A packed chunk declared relative to an ancestor and an exact path. -/
abbrev PackedCheckedAtPath
    (terms : ℕ) (ancestor : CertificateBox) (path : Path) :=
  PackedCheckedChunk terms (follow ancestor path)

/-- The corresponding semantic checked chunk at a relative path. -/
abbrev CheckedAtPath
    (terms : ℕ) (ancestor : CertificateBox) (path : Path) :=
  Auto.CheckedChunk terms (follow ancestor path)

abbrev oneToTwoRootAt (path : Path) : CertificateBox :=
  follow Auto.oneToTwoRoot path

abbrev twoToFourRootAt (path : Path) : CertificateBox :=
  follow Auto.twoToFourRoot path

/-- Concise generated-data type for a chunk under the `[1,2]` historical
root. -/
abbrev OneToTwoPackedChunk (terms : ℕ) (path : Path) :=
  PackedCheckedChunk terms (oneToTwoRootAt path)

/-- Concise generated-data type for a chunk under the `[2,4]` historical
root. -/
abbrev TwoToFourPackedChunk (terms : ℕ) (path : Path) :=
  PackedCheckedChunk terms (twoToFourRootAt path)

abbrev OneToTwoCheckedChunk (terms : ℕ) (path : Path) :=
  Auto.CheckedChunk terms (oneToTwoRootAt path)

abbrev TwoToFourCheckedChunk (terms : ℕ) (path : Path) :=
  Auto.CheckedChunk terms (twoToFourRootAt path)

/-! ## Proof-preserving structural joins -/

/-- Join two already checked midpoint children at an arbitrary exact root. -/
def join
    {terms : ℕ} {root : CertificateBox} (axis : CertificateAxis)
    (lower : Auto.CheckedChunk terms
      (root.lower axis (Auto.axisCut root axis)))
    (upper : Auto.CheckedChunk terms
      (root.upper axis (Auto.axisCut root axis))) :
    Auto.CheckedChunk terms root :=
  LRUpperKHistoricalAutoTree.CheckedTree.join axis lower upper

def joinS
    {terms : ℕ} {root : CertificateBox}
    (lower : Auto.CheckedChunk terms
      (root.lower .s (Auto.axisCut root .s)))
    (upper : Auto.CheckedChunk terms
      (root.upper .s (Auto.axisCut root .s))) :
    Auto.CheckedChunk terms root :=
  join .s lower upper

def joinK
    {terms : ℕ} {root : CertificateBox}
    (lower : Auto.CheckedChunk terms
      (root.lower .k (Auto.axisCut root .k)))
    (upper : Auto.CheckedChunk terms
      (root.upper .k (Auto.axisCut root .k))) :
    Auto.CheckedChunk terms root :=
  join .k lower upper

def joinH
    {terms : ℕ} {root : CertificateBox}
    (lower : Auto.CheckedChunk terms
      (root.lower .chi (Auto.axisCut root .chi)))
    (upper : Auto.CheckedChunk terms
      (root.upper .chi (Auto.axisCut root .chi))) :
    Auto.CheckedChunk terms root :=
  join .chi lower upper

/-- Join children named by their natural full paths below a generated parent
path.  The two path equalities above perform the only dependent transport. -/
def joinAtPath
    {terms : ℕ} {ancestor : CertificateBox}
    (path : Path) (axis : CertificateAxis)
    (lower : CheckedAtPath terms ancestor
      (path ++ [lowerStep axis]))
    (upper : CheckedAtPath terms ancestor
      (path ++ [upperStep axis])) :
    CheckedAtPath terms ancestor path :=
  join axis
    (by
      simpa only [CheckedAtPath, follow_append_lower] using lower)
    (by
      simpa only [CheckedAtPath, follow_append_upper] using upper)

/-- A checked chunk at the empty relative path is definitionally a checked
tree at its ancestor root. -/
def checkedTreeOfEmptyPath
    {terms : ℕ} {root : CertificateBox}
    (chunk : CheckedAtPath terms root []) : Auto.CheckedTree terms root := by
  simpa [CheckedAtPath, follow, Auto.follow] using chunk

/-! ## Exact rejection behavior -/

theorem decode_mean : decode "M" = some (.accept ()) := by rfl
theorem decode_empty : decode "" = none := by rfl
theorem decode_incomplete_split : decode "s" = none := by rfl
theorem decode_incomplete_upper : decode "hM" = none := by rfl
theorem decode_trailing : decode "MM" = none := by rfl
theorem decode_invalid : decode "?" = none := by rfl

end LRUpperKHistoricalPackedCertificate
end CourtadeKumar
