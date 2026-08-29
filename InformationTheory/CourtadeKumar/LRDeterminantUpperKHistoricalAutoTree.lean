import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalConcreteSoundness

/-!
# Compact midpoint trees for the historical upper-`K` replay

The historical replay has one analytic leaf kind.  An accepted leaf therefore
stores only `Unit`, while a split stores only its coordinate axis.  The exact
rational midpoint is reconstructed from the current box during traversal.

External topology generation carries no proof authority.  `Tree.check`
recomputes the complete historical centered checker at every accepted box,
and `target_nonnegative_of_check` is an ordinary structural proof reducing
each accepted leaf to the concrete evaluator soundness theorem.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalAutoTree

open LRUpperKReplayCertificate

namespace Concrete

abbrev check := LRUpperKHistoricalConcreteEvaluator.check

end Concrete

/-! ## Compact topology and executable traversal -/

/-- Exact ordinary midpoint on the selected coordinate of the current box. -/
def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

/-- Which child of an exact midpoint split is followed by one path step. -/
inductive Branch where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- One axis-and-side step toward an independently replayed chunk root. -/
structure Step where
  axis : CertificateAxis
  branch : Branch
  deriving DecidableEq, Repr

abbrev Path := List Step

/-- Follow one exact historical midpoint step. -/
def descend (box : CertificateBox) (step : Step) : CertificateBox :=
  let cut := axisCut box step.axis
  match step.branch with
  | .lower => box.lower step.axis cut
  | .upper => box.upper step.axis cut

/-- Recover an arbitrary chunk root from an ancestor and a midpoint path. -/
def follow : CertificateBox → Path → CertificateBox
  | box, [] => box
  | box, step :: rest => follow (descend box step) rest

/-- Compact historical topology.  The `Unit` argument makes explicit that an
accepted leaf contains no analytic payload. -/
inductive Tree where
  | accept (unit : Unit)
  | split (axis : CertificateAxis) (lower upper : Tree)
  deriving Repr

namespace Tree

/-- Traverse a compact tree with the concrete historical checker.  The
historically audited parameters use square-root fuel `40` and logarithm fuel
`48`; only the Taylor-term count is left as a tree parameter. -/
def check (terms : ℕ) : Tree → CertificateBox → Bool
  | .accept _, box => Concrete.check terms 40 48 box
  | .split axis lower upper, box =>
      let cut := axisCut box axis
      check terms lower (box.lower axis cut) &&
        check terms upper (box.upper axis cut)

def nodeCount : Tree → ℕ
  | .accept _ => 1
  | .split _ lower upper => 1 + nodeCount lower + nodeCount upper

def leafCount : Tree → ℕ
  | .accept _ => 1
  | .split _ lower upper => leafCount lower + leafCount upper

def maxDepth : Tree → ℕ
  | .accept _ => 0
  | .split _ lower upper => 1 + max (maxDepth lower) (maxDepth upper)

/-- One-byte preorder grammar used by the historical artifacts: `M` is a
mean-value leaf and `s`/`k`/`h` are midpoint splits. -/
def tokens : Tree → List Char
  | .accept _ => ['M']
  | .split axis lower upper =>
      (match axis with | .s => 's' | .k => 'k' | .chi => 'h') ::
        (tokens lower ++ tokens upper)

def packed (tree : Tree) : String := String.ofList tree.tokens

/-- The split checker is definitionally the conjunction of the two child
checks at the reconstructed midpoint boxes. -/
theorem split_check_eq_true_iff
    {terms : ℕ} {root : CertificateBox} {axis : CertificateAxis}
    {lower upper : Tree} :
    (Tree.split axis lower upper).check terms root = true ↔
      lower.check terms (root.lower axis (axisCut root axis)) = true ∧
        upper.check terms (root.upper axis (axisCut root axis)) = true := by
  simp [Tree.check]

end Tree

/-! ## Structural soundness -/

/-- A successful compact traversal proves the historical target nonnegative
at every relevant point in the current box. -/
theorem target_nonnegative_of_check
    {terms : ℕ} {box : CertificateBox} {tree : Tree}
    (hcheck : tree.check terms box = true) :
    ∀ coordinate, box.Contains coordinate → CenteredRelevant coordinate →
      0 ≤ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate) := by
  induction tree generalizing box with
  | accept unit =>
      intro coordinate hcoordinate hrelevant
      exact LRUpperKHistoricalConcreteSoundness.nonnegative_of_check
        terms (by simpa [Tree.check] using hcheck)
        hcoordinate hrelevant
  | split axis lower upper lower_ih upper_ih =>
      have hchildren :
          lower.check terms (box.lower axis (axisCut box axis)) = true ∧
            upper.check terms (box.upper axis (axisCut box axis)) = true := by
        simpa [Tree.check, Bool.and_eq_true] using hcheck
      intro coordinate hcoordinate hrelevant
      rcases box.contains_lower_or_upper hcoordinate axis
          (axisCut box axis) with hlower | hupper
      · exact lower_ih hchildren.1 coordinate hlower hrelevant
      · exact upper_ih hchildren.2 coordinate hupper hrelevant

/-- A compact tree together with the kernel equality establishing successful
traversal from an arbitrary root.  Arbitrary roots are useful for independently
checked packed chunks and their later structural joins. -/
structure CheckedTree (terms : ℕ) (root : CertificateBox) where
  certificate : Tree
  checked : certificate.check terms root = true

/-- Synonym emphasizing the arbitrary-root use in generated replay groups. -/
abbrev CheckedChunk (terms : ℕ) (root : CertificateBox) :=
  CheckedTree terms root

namespace CheckedTree

theorem target_nonnegative
    {terms : ℕ} {root : CertificateBox}
    (tree : CheckedTree terms root)
    {coordinate : CertificatePoint} (hcoordinate : root.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) :=
  target_nonnegative_of_check tree.checked coordinate hcoordinate hrelevant

/-- Join two independently checked midpoint children without replaying their
internal arithmetic. -/
def join
    {terms : ℕ} {root : CertificateBox} (axis : CertificateAxis)
    (lower : CheckedTree terms
      (root.lower axis (axisCut root axis)))
    (upper : CheckedTree terms
      (root.upper axis (axisCut root axis))) :
    CheckedTree terms root where
  certificate := .split axis lower.certificate upper.certificate
  checked := Tree.split_check_eq_true_iff.mpr
    ⟨lower.checked, upper.checked⟩

def joinS
    {terms : ℕ} {root : CertificateBox}
    (lower : CheckedTree terms
      (root.lower .s (axisCut root .s)))
    (upper : CheckedTree terms
      (root.upper .s (axisCut root .s))) :
    CheckedTree terms root :=
  join .s lower upper

def joinK
    {terms : ℕ} {root : CertificateBox}
    (lower : CheckedTree terms
      (root.lower .k (axisCut root .k)))
    (upper : CheckedTree terms
      (root.upper .k (axisCut root .k))) :
    CheckedTree terms root :=
  join .k lower upper

def joinChi
    {terms : ℕ} {root : CertificateBox}
    (lower : CheckedTree terms
      (root.lower .chi (axisCut root .chi)))
    (upper : CheckedTree terms
      (root.upper .chi (axisCut root .chi))) :
    CheckedTree terms root :=
  join .chi lower upper

end CheckedTree

/-! ## Exact upper-`K` roots and determinant-region adapter -/

abbrev oneToTwoRoot : CertificateBox :=
  lrDeterminantUpperKKChartRoot.lower .k 2

abbrev twoToFourRoot : CertificateBox :=
  lrDeterminantUpperKKChartRoot.upper .k 2

/-- Any checked historical tree whose root contains an encoded region supplies
that determinant-ledger row. -/
theorem regionCertificate_of_checkedTree
    {terms : ℕ} {root : CertificateBox}
    {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : CheckedTree terms root) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hchartRelevant : CenteredRelevant
      (lrDeterminantKChartEncode point) := by
    unfold CenteredRelevant
    rw [hdecoded]
    exact ⟨hinterior, hrelevant⟩
  have htarget := tree.target_nonnegative
    (root_contains hinterior hregion) hchartRelevant
  rw [hdecoded] at htarget
  exact lrDeterminantAdmittedTarget_of_upperKReplayTarget hinterior htarget

/-- The two separately rooted historical trees cover the exact upper-`K`
region; their shared `K = 2` face is handled by the generic box split lemma. -/
theorem upperKRegionCertificate_of_twoCheckedTrees
    {terms12 terms24 : ℕ}
    (tree12 : CheckedTree terms12 oneToTwoRoot)
    (tree24 : CheckedTree terms24 twoToFourRoot) :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hchartRelevant : CenteredRelevant
      (lrDeterminantKChartEncode point) := by
    unfold CenteredRelevant
    rw [hdecoded]
    exact ⟨hinterior, hrelevant⟩
  have hroot :=
    lrDeterminantUpperKKChartRoot_contains_encode hinterior hregion
  rcases CertificateBox.contains_lower_or_upper hroot .k 2 with h12 | h24
  · have htarget := tree12.target_nonnegative h12 hchartRelevant
    rw [hdecoded] at htarget
    exact lrDeterminantAdmittedTarget_of_upperKReplayTarget
      hinterior htarget
  · have htarget := tree24.target_nonnegative h24 hchartRelevant
    rw [hdecoded] at htarget
    exact lrDeterminantAdmittedTarget_of_upperKReplayTarget
      hinterior htarget

end LRUpperKHistoricalAutoTree
end CourtadeKumar
