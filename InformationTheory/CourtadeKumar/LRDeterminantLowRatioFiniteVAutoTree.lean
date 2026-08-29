import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVDiscard

/-!
# Compact automatic trees for the finite low-ratio direct-`V` replay

The concrete direct-`V` oracle carries large deterministic interval payloads.
Serializing one copy at every accepted leaf would make a generated tree much
larger than its actual topology.  This module therefore stores only an
`AcceptTag`: either the natural whole-box rule or the correlated mean-value
rule.  `materialize` reconstructs the corresponding checked payload from the
exact current child box before converting the result to the existing
`LRLowRatioFiniteVMeanValue.CheckedTree` interface.

The tree builder is untrusted convenience code.  Its correctness theorem is
an ordinary structural proof: a returned accept tag is justified by one of
the executable Boolean checkers, a returned discard tag is justified by the
endpoint-safe discard checker, and split nodes combine the two induction
hypotheses.  No compiler-backed decision procedure is used.
-/

namespace CourtadeKumar
namespace LRLowRatioFiniteVAutoTree

/-! ## Compact accepted leaves and their executable checker -/

/-- The only datum stored at an accepted leaf. -/
inductive AcceptTag where
  | natural
  | meanValue
  deriving DecidableEq, Repr

/-- Direct executable checker for a compact accept tag. -/
def acceptCheck (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : AcceptTag → Bool
  | .natural =>
      LRLowRatioFiniteVConcreteOracle.autoNaturalAccepts
        terms sqrtFuel logFuel box
  | .meanValue =>
      LRLowRatioFiniteVConcreteOracle.autoMeanAccepts
        terms sqrtFuel logFuel box

/-- Try the cheaper natural enclosure first, then the correlated mean-value
rule.  Returning a tag does not assert anything until `acceptCheck` is run. -/
def autoAccept (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Option AcceptTag :=
  if LRLowRatioFiniteVConcreteOracle.autoNaturalAccepts
      terms sqrtFuel logFuel box then
    some .natural
  else if LRLowRatioFiniteVConcreteOracle.autoMeanAccepts
      terms sqrtFuel logFuel box then
    some .meanValue
  else
    none

/-- An automatically proposed accept tag passes its direct checker. -/
theorem autoAccept_check_of_eq (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (tag : AcceptTag)
    (hauto : autoAccept terms sqrtFuel logFuel box = some tag) :
    acceptCheck terms sqrtFuel logFuel box tag = true := by
  unfold autoAccept at hauto
  split at hauto <;> rename_i hnatural
  · cases hauto
    simpa [acceptCheck] using hnatural
  split at hauto <;> rename_i hmean
  · cases hauto
    simpa [acceptCheck] using hmean
  · simp at hauto

/-! ## Box-dependent materialization -/

/-- Reconstruct the full checked leaf payload from a compact tag and the
current box reached by the subdivision traversal. -/
def materializeLeaf (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : AcceptTag →
      LRLowRatioFiniteVMeanValue.LeafPayload
        (LRLowRatioFiniteVConcreteOracle.concreteOracle terms)
  | .natural =>
      .natural (LRLowRatioFiniteVConcreteOracle.auto
        sqrtFuel logFuel box)
  | .meanValue =>
      .meanValue (LRLowRatioFiniteVConcreteOracle.autoCentered
        terms sqrtFuel logFuel box)

/-- Materializing a tag changes neither its executable acceptance Boolean
nor the analytic rule selected by that tag. -/
theorem leafAccepts_materializeLeaf (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (tag : AcceptTag) :
    LRLowRatioFiniteVMeanValue.leafAccepts
        (LRLowRatioFiniteVConcreteOracle.concreteOracle terms) box
        (materializeLeaf terms sqrtFuel logFuel box tag) =
      acceptCheck terms sqrtFuel logFuel box tag := by
  cases tag with
  | natural =>
      simpa [materializeLeaf, acceptCheck] using
        (LRLowRatioFiniteVConcreteOracle.autoNaturalAccepts_eq
          terms sqrtFuel logFuel box).symm
  | meanValue =>
      simpa [materializeLeaf, acceptCheck,
        LRLowRatioFiniteVMeanValue.leafAccepts] using
        (LRLowRatioFiniteVConcreteOracle.autoMeanAccepts_eq
          terms sqrtFuel logFuel box).symm

/-- Exact midpoint cut associated with one axis of the current box. -/
def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

/-- Compact midpoint topology used by the direct-`V` generator.  Accept and
discard leaves contain only tags, and each split stores only its axis: the
exact rational midpoint is reconstructed from the current box. -/
inductive Tree where
  | accept (tag : AcceptTag)
  | discard (data : LRLowRatioFiniteVDiscard.DiscardData)
  | split (axis : CertificateAxis) (lower upper : Tree)
  deriving Repr

namespace Tree

/-- Total number of internal nodes and leaves in a compact topology. -/
def nodeCount : Tree → ℕ
  | .accept _ => 1
  | .discard _ => 1
  | .split _ lower upper => 1 + nodeCount lower + nodeCount upper

/-- Number of accepted or discarded terminal boxes. -/
def leafCount : Tree → ℕ
  | .accept _ => 1
  | .discard _ => 1
  | .split _ lower upper => leafCount lower + leafCount upper

/-- Largest number of split edges from the root to a leaf.  A one-leaf tree
has depth zero. -/
def maxDepth : Tree → ℕ
  | .accept _ => 0
  | .discard _ => 0
  | .split _ lower upper => 1 + max (maxDepth lower) (maxDepth upper)

/-- Traverse the compact midpoint topology with its direct executable
checkers. -/
def check (terms sqrtFuel logFuel : ℕ) :
    Tree → CertificateBox → Bool
  | .accept tag, box => acceptCheck terms sqrtFuel logFuel box tag
  | .discard data, box =>
      LRLowRatioFiniteVDiscard.discardCheck
        terms sqrtFuel logFuel box data
  | .split axis lower upper, box =>
      let cut := axisCut box axis
      check terms sqrtFuel logFuel lower (box.lower axis cut) &&
        check terms sqrtFuel logFuel upper (box.upper axis cut)

end Tree

/-- Recursively reconstruct full accepted payloads at the exact boxes seen
by the generic subdivision checker.  Discard tags and split topology are
preserved verbatim. -/
def materialize (terms sqrtFuel logFuel : ℕ) :
    CertificateBox → Tree →
      SubdivisionCertificate
        (LRLowRatioFiniteVMeanValue.LeafPayload
          (LRLowRatioFiniteVConcreteOracle.concreteOracle terms))
        LRLowRatioFiniteVDiscard.DiscardData
  | box, .accept tag =>
      .accept (materializeLeaf terms sqrtFuel logFuel box tag)
  | _box, .discard data => .discard data
  | box, .split axis lower upper =>
      let cut := axisCut box axis
      .split axis cut
        (materialize terms sqrtFuel logFuel
          (box.lower axis cut) lower)
        (materialize terms sqrtFuel logFuel
          (box.upper axis cut) upper)

/-- Exact checker commutation for recursive materialization.  This equality
is the key compactness boundary: a kernel check of the tag tree is literally
the check required by the existing payload-carrying tree after materializing
each current box. -/
theorem materialize_check (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (tree : Tree) :
    (materialize terms sqrtFuel logFuel box tree).check
        (LRLowRatioFiniteVMeanValue.leafAccepts
          (LRLowRatioFiniteVConcreteOracle.concreteOracle terms))
        (LRLowRatioFiniteVDiscard.discardCheck
          terms sqrtFuel logFuel) box =
      tree.check terms sqrtFuel logFuel box := by
  induction tree generalizing box with
  | accept tag =>
      simpa [materialize, SubdivisionCertificate.check] using
        leafAccepts_materializeLeaf terms sqrtFuel logFuel box tag
  | discard data =>
      rfl
  | split axis lower upper lower_ih upper_ih =>
      simp only [materialize, Tree.check,
        SubdivisionCertificate.check]
      rw [lower_ih, upper_ih]

/-! ## Deterministic split heuristic -/

/-- Mean-value loss attributed to the `s` radius. -/
def splitScoreS (box : CertificateBox)
    (evaluation : MidpointSKCertificate) : ℚ :=
  evaluation.derivS.maxAbs *
    RationalEnclosure.radius box.sInterval

/-- Mean-value loss attributed to the `K` radius. -/
def splitScoreK (box : CertificateBox)
    (evaluation : MidpointSKCertificate) : ℚ :=
  evaluation.derivK.maxAbs *
    RationalEnclosure.radius box.kInterval

/-- The mean-value rule keeps the full endpoint-safe `h` interval in its
center value.  Its value radius is therefore a direct target-scale proxy for
the uncertainty removable by splitting `h`; no potentially singular
`h`-derivative enclosure is needed. -/
def splitScoreChi (box : CertificateBox)
    (evaluation : MidpointSKCertificate) : ℚ :=
  if box.chiLo < box.chiHi then
    RationalEnclosure.radius evaluation.value
  else
    0

/-- Deterministic positive-width fallback used only if every target-scale
score vanishes. -/
def widestAxis (box : CertificateBox) : CertificateAxis :=
  let ws := RationalEnclosure.radius box.sInterval
  let wk := RationalEnclosure.radius box.kInterval
  let wh := RationalEnclosure.radius box.chiInterval
  if ws ≥ wk ∧ ws ≥ wh ∧ box.sLo < box.sHi then .s
  else if wk ≥ wh ∧ box.kLo < box.kHi then .k
  else if box.chiLo < box.chiHi then .chi
  else if box.sLo < box.sHi then .s
  else .k

/-- Production splitter choosing the largest target-scale loss, with
deterministic tie order `s`, then `K`, then `h`.  The whole evaluation is
bound once so the three scores share the same exact interval graph.  This
choice costs one extra graph at each unresolved node, but empirical Lean
probes produce substantially shallower terminal boxes for the endpoint-safe
two-coordinate mean-value rule, reducing the dominant final kernel replay. -/
def chooseTargetAxis (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : CertificateAxis :=
  let evaluation := LRLowRatioFiniteVConcreteOracle.autoEvaluation
    terms sqrtFuel logFuel box
  let ss := splitScoreS box evaluation
  let sk := splitScoreK box evaluation
  let sc := splitScoreChi box evaluation
  if ss = 0 ∧ sk = 0 ∧ sc = 0 then widestAxis box
  else if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
  else if sk ≥ sc ∧ box.kLo < box.kHi then .k
  else if box.chiLo < box.chiHi then .chi
  else if box.sLo < box.sHi then .s
  else .k

/-- Historical diagnostic splitter, comparing the relative widths

`(sHi-sLo)/sLo`, `(kHi-kLo)/kLo`, and `chiHi-chiLo`

by exact cross-products.  On the positive finite-`V` chart this is precisely
the rule used by the audited generator.  It remains available for comparison
and rescue experiments, while the production builder uses `chooseTargetAxis`.
Explicit endpoint and positive-width guards extend it safely to boxes with a
zero lower endpoint or a degenerate axis, without ever selecting a zero-width
axis while another axis can split.  Ties retain the historical order `s`,
then `K`, then `h`. -/
def chooseHistoricalAxis (box : CertificateBox) : CertificateAxis :=
  let ds := box.sHi - box.sLo
  let dk := box.kHi - box.kLo
  let dh := box.chiHi - box.chiLo
  let canS := box.sLo < box.sHi
  let canK := box.kLo < box.kHi
  let canH := box.chiLo < box.chiHi
  if canS ∧ box.sLo ≤ 0 then .s
  else if canK ∧ box.kLo ≤ 0 then .k
  else if canS ∧
      (¬ canK ∨ dk * box.sLo ≤ ds * box.kLo) ∧
      (¬ canH ∨ dh * box.sLo ≤ ds) then .s
  else if canK ∧ (¬ canH ∨ dh * box.kLo ≤ dk) then .k
  else if canH then .chi
  else if canS then .s
  else .k

/-! ## Compact deterministic builder -/

/-- Build only compact tags and split topology.  Accepted leaves are tried
before discards so a successful inexpensive natural or mean-value check does
not compute the larger nonpositive-`J` discard graph.  Nested child matches
also avoid computing the upper child after a failed lower child. -/
def buildTree (terms sqrtFuel logFuel : ℕ) :
    ℕ → CertificateBox → Option Tree
  | 0, box =>
      match autoAccept terms sqrtFuel logFuel box with
      | some tag => some (.accept tag)
      | none =>
          match LRLowRatioFiniteVDiscard.autoDiscard
              terms sqrtFuel logFuel box with
          | some data => some (.discard data)
          | none => none
  | fuel + 1, box =>
      match autoAccept terms sqrtFuel logFuel box with
      | some tag => some (.accept tag)
      | none =>
          match LRLowRatioFiniteVDiscard.autoDiscard
              terms sqrtFuel logFuel box with
          | some data => some (.discard data)
          | none =>
              let axis := chooseTargetAxis terms sqrtFuel logFuel box
              let cut := axisCut box axis
              match buildTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) with
              | none => none
              | some lower =>
                  match buildTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) with
                  | none => none
                  | some upper =>
                      some (.split axis lower upper)

/-- A successful compact build passes the ordinary tag and discard
checkers.  The proof is structural and does not evaluate any concrete root. -/
theorem buildTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox)
    (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check terms sqrtFuel logFuel box = true := by
  induction fuel generalizing box tree with
  | zero =>
      generalize haccept :
        autoAccept terms sqrtFuel logFuel box = acceptOption
      cases acceptOption with
      | some tag =>
          simp [buildTree, haccept] at hbuild
          subst tree
          simpa [Tree.check] using
            autoAccept_check_of_eq
              terms sqrtFuel logFuel box tag haccept
      | none =>
          generalize hdiscard :
            LRLowRatioFiniteVDiscard.autoDiscard
              terms sqrtFuel logFuel box = discardOption
          cases discardOption with
          | none =>
              simp [buildTree, haccept, hdiscard] at hbuild
          | some data =>
              simp [buildTree, haccept, hdiscard] at hbuild
              subst tree
              simpa [Tree.check] using
                LRLowRatioFiniteVDiscard.autoDiscard_check_of_eq
                  terms sqrtFuel logFuel box data hdiscard
  | succ fuel ih =>
      generalize haccept :
        autoAccept terms sqrtFuel logFuel box = acceptOption
      cases acceptOption with
      | some tag =>
          simp [buildTree, haccept] at hbuild
          subst tree
          simpa [Tree.check] using
            autoAccept_check_of_eq
              terms sqrtFuel logFuel box tag haccept
      | none =>
          generalize hdiscard :
            LRLowRatioFiniteVDiscard.autoDiscard
              terms sqrtFuel logFuel box = discardOption
          cases discardOption with
          | some data =>
              simp [buildTree, haccept, hdiscard] at hbuild
              subst tree
              simpa [Tree.check] using
                LRLowRatioFiniteVDiscard.autoDiscard_check_of_eq
                  terms sqrtFuel logFuel box data hdiscard
          | none =>
              let axis := chooseTargetAxis terms sqrtFuel logFuel box
              let cut := axisCut box axis
              generalize hlower :
                buildTree terms sqrtFuel logFuel fuel
                  (box.lower axis cut) = lowerOption
              cases lowerOption with
              | none =>
                  simp [buildTree, haccept, hdiscard, axis, cut,
                    hlower] at hbuild
              | some lower =>
                  generalize hupper :
                    buildTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) = upperOption
                  cases upperOption with
                  | none =>
                      simp [buildTree, haccept, hdiscard, axis, cut,
                        hlower, hupper] at hbuild
                  | some upper =>
                      simp [buildTree, haccept, hdiscard, axis, cut,
                        hlower, hupper] at hbuild
                      subst tree
                      simp only [Tree.check, Bool.and_eq_true]
                      exact ⟨ih _ _ hlower, ih _ _ hupper⟩

/-! ## Existing checked-tree interface -/

/-- A compact tag tree together with its ordinary Boolean traversal. -/
structure AutoTaggedCheckedTree
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  certificate : Tree
  checked : certificate.check terms sqrtFuel logFuel root = true

namespace AutoTaggedCheckedTree

/-- Materialize a compact checked tree into the pre-existing semantic
interface.  All downstream finite-band theorems can therefore remain
unchanged. -/
def toCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : AutoTaggedCheckedTree terms sqrtFuel logFuel root) :
    LRLowRatioFiniteVMeanValue.CheckedTree
      (LRLowRatioFiniteVConcreteOracle.concreteOracle terms) root where
  DiscardData := LRLowRatioFiniteVDiscard.DiscardData
  discardCheck := LRLowRatioFiniteVDiscard.discardCheck
    terms sqrtFuel logFuel
  discardSound := LRLowRatioFiniteVDiscard.discardCheck_sound
    terms sqrtFuel logFuel
  certificate := materialize terms sqrtFuel logFuel root tree.certificate
  checked := by
    rw [materialize_check]
    exact tree.checked

/-- Package any successfully built topology at the compact checked-tree
boundary. -/
def ofBuildTreeEq
    {terms sqrtFuel logFuel fuel : ℕ} {root : CertificateBox}
    (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel root = some tree) :
    AutoTaggedCheckedTree terms sqrtFuel logFuel root where
  certificate := tree
  checked := buildTree_check_of_eq
    terms sqrtFuel logFuel fuel root tree hbuild

end AutoTaggedCheckedTree

end LRLowRatioFiniteVAutoTree
end CourtadeKumar
