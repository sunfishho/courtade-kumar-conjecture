import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVFirstBracketForest

/-!
# Compact hybrid trees for the finite low-ratio first bracket

The historical lower finite-`V` replay used a hybrid accepted-leaf rule.  It
first tried the sharp natural whole-box enclosure and, only when interval
dependency defeated that test, tried the sharp centered `(s,K)` mean-value
enclosure.  This module records that rule without serializing either analytic
payload: an accepted leaf stores only `natural` or `meanValue`, and the trusted
checker reconstructs the relevant auto payload from the exact current box.

Internal topology is midpoint/axis-only.  A separate ten-slab adapter joins
the fixed historical dyadic `s` roots with explicit cuts; its proof combines
the already checked slab equalities structurally and performs no aggregate
arithmetic replay.
-/

namespace CourtadeKumar

namespace LRDeterminantLowRatioFiniteVFirstBracketAutoTree

open LRUpperKReplayCertificate
open LRLowRatioFiniteVMeanValue
open LRLowRatioFiniteVMeanValue.FirstBracketForest

/-! ## Compact hybrid accepted leaves -/

/-- The historical rule selected either a natural sharp enclosure or the
correlated sharp centered mean-value enclosure. -/
inductive AcceptTag where
  | natural
  | meanValue
  deriving DecidableEq, Repr

/-- Reconstruct and check the cheaper sharp whole-box enclosure. -/
def naturalAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  let payload := auto sqrtFuel logFuel box
  payloadCheck box payload &&
    (sharpEnclose terms box payload).provesNonnegative

/-- Direct executable checker for a compact hybrid tag. -/
def acceptCheck (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : AcceptTag → Bool
  | .natural => naturalAccepts terms sqrtFuel logFuel box
  | .meanValue =>
      autoSharpCenteredAccepts terms sqrtFuel logFuel box ()

/-- Try the historical natural rule first, followed by sharp centered
mean value.  The returned tag has no authority until `acceptCheck` succeeds. -/
def autoAccept (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Option AcceptTag :=
  if naturalAccepts terms sqrtFuel logFuel box then
    some .natural
  else if autoSharpCenteredAccepts terms sqrtFuel logFuel box () then
    some .meanValue
  else
    none

/-- Any automatically proposed tag passes its direct Boolean checker. -/
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

/-! ## Soundness of the two hybrid tags -/

/-- The centered tag includes the open-chart check needed to recover the
positive square root `h` from the decoded condition `0 < h² < 1`. -/
private theorem nonnegative_of_autoSharpMeanAccepts
    (terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    (haccept :
      autoSharpCenteredAccepts terms sqrtFuel logFuel box () = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hinterior :
      LRHighShapeInterior (lrDeterminantKChartDecode coordinate)) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hsharp :
      sharpCenteredAccepts terms box
        (autoCentered sqrtFuel logFuel box) = true := by
    simpa [autoSharpCenteredAccepts] using haccept
  have hacceptParts :
      centeredPayloadCheck box (autoCentered sqrtFuel logFuel box) = true ∧
        (evaluateSharpCentered terms box
          (autoCentered sqrtFuel logFuel box)).check box = true := by
    simpa [sharpCenteredAccepts] using hsharp
  have hpayloadParts :
      (openChartBoxCheck box = true ∧
        payloadCheck (LRUpperKReplayCertificate.centerSKBox box)
          (autoCentered sqrtFuel logFuel box).center = true) ∧
      payloadCheck box
        (autoCentered sqrtFuel logFuel box).derivative = true := by
    simpa [centeredPayloadCheck] using hacceptParts.1
  have hopenParts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
    simpa [openChartBoxCheck] using hpayloadParts.1.1
  have hhNonnegative : 0 ≤ coordinate.chi := by
    have hlo : (0 : ℝ) ≤ box.chiLo := by
      exact_mod_cast hopenParts.2.2.2.2.2.2.1
    exact hlo.trans hcoordinate.2.2.2.2.1
  have hhSqPos : 0 < coordinate.chi ^ 2 := by
    simpa [lrDeterminantKChartDecode] using hinterior.2.2.1
  have hhSqLt : coordinate.chi ^ 2 < 1 := by
    simpa [lrDeterminantKChartDecode] using hinterior.2.2.2
  have hhPositive : 0 < coordinate.chi := by nlinarith
  have hhOne : coordinate.chi < 1 := by nlinarith
  exact (positive_of_sharpCenteredAccepts terms hsharp hcoordinate
    hhPositive hhOne).le

/-- Either compact accepted tag proves the sharp upper-`K` replay target
nonnegative throughout its current box, conditional only on the decoded
interior needed by the mean-value tag. -/
theorem nonnegative_of_acceptCheck
    (terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox} {tag : AcceptTag}
    (haccept : acceptCheck terms sqrtFuel logFuel box tag = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hinterior :
      LRHighShapeInterior (lrDeterminantKChartDecode coordinate)) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  cases tag with
  | natural =>
      have hparts :
          payloadCheck box (auto sqrtFuel logFuel box) = true ∧
          (sharpEnclose terms box
            (auto sqrtFuel logFuel box)).provesNonnegative = true := by
        simpa [acceptCheck, naturalAccepts] using haccept
      exact RationalEnclosure.nonnegative_of_provesNonnegative hparts.2
        (sharpEnclose_sound terms hparts.1 hcoordinate)
  | meanValue =>
      exact nonnegative_of_autoSharpMeanAccepts
        terms sqrtFuel logFuel (by
          simpa [acceptCheck] using haccept) hcoordinate hinterior

/-! ## Compact midpoint topology and materialization -/

/-- Exact midpoint cut for an axis of the current box. -/
def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

/-- A compact tree stores an accepted tag or a split axis, but no rational
cut and no analytic payload. -/
inductive Tree where
  | accept (tag : AcceptTag)
  | split (axis : CertificateAxis) (lower upper : Tree)
  deriving Repr

namespace Tree

/-- Total compact topology nodes, including accepted leaves. -/
def nodeCount : Tree → ℕ
  | .accept _tag => 1
  | .split _axis lower upper =>
      1 + nodeCount lower + nodeCount upper

/-- Number of accepted terminal leaves. -/
def leafCount : Tree → ℕ
  | .accept _tag => 1
  | .split _axis lower upper =>
      leafCount lower + leafCount upper

/-- Maximum number of split edges from the root to an accepted leaf. -/
def maxDepth : Tree → ℕ
  | .accept _tag => 0
  | .split _axis lower upper =>
      1 + max (maxDepth lower) (maxDepth upper)

/-- Traverse a compact tree with the two hybrid executable leaf checks. -/
def check (terms sqrtFuel logFuel : ℕ) :
    Tree → CertificateBox → Bool
  | .accept tag, box => acceptCheck terms sqrtFuel logFuel box tag
  | .split axis lower upper, box =>
      let cut := axisCut box axis
      check terms sqrtFuel logFuel lower (box.lower axis cut) &&
        check terms sqrtFuel logFuel upper (box.upper axis cut)

end Tree

/-- A generic checked certificate cannot contain a successful discard leaf. -/
def noDiscard (_box : CertificateBox) (_data : Unit) : Bool := false

/-- Reconstruct the exact rational midpoint cuts reached during traversal. -/
def materialize : CertificateBox → Tree →
    SubdivisionCertificate AcceptTag Unit
  | _box, .accept tag => .accept tag
  | box, .split axis lower upper =>
      let cut := axisCut box axis
      .split axis cut
        (materialize (box.lower axis cut) lower)
        (materialize (box.upper axis cut) upper)

/-- Materialization commutes exactly with the compact checker. -/
theorem materialize_check (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (tree : Tree) :
    (materialize box tree).check
        (acceptCheck terms sqrtFuel logFuel) noDiscard box =
      tree.check terms sqrtFuel logFuel box := by
  induction tree generalizing box with
  | accept tag => rfl
  | split axis lower upper lower_ih upper_ih =>
      simp only [materialize, Tree.check, SubdivisionCertificate.check]
      rw [lower_ih, upper_ih]

/-! ## Semantic checked-certificate boundary -/

/-- Any successfully checked hybrid subdivision certificate supplies the
abstract first-bracket tree used by the finite-`V` assembly. -/
def firstBracketTreeOfCheckedCertificate
    (terms sqrtFuel logFuel : ℕ)
    {root : CertificateBox}
    (certificate : SubdivisionCertificate AcceptTag Unit)
    (checked : certificate.check
      (acceptCheck terms sqrtFuel logFuel) noDiscard root = true) :
    FirstBracketTree root where
  target_nonnegative := by
    intro coordinate hcoordinate hinterior _hrelevant
    have hconditional := subdivisionCertificate_sound
      (Relevant := fun _coordinate : CertificatePoint ↦ True)
      (Property := fun coordinate ↦
        LRHighShapeInterior (lrDeterminantKChartDecode coordinate) →
          0 ≤ lrFiniteDeterminantUpperKReplayTarget
            (lrDeterminantKChartDecode coordinate))
      (acceptBox := acceptCheck terms sqrtFuel logFuel)
      (discardBox := noDiscard)
      (box := root) (certificate := certificate)
      (by
        intro box tag haccept point hpoint
        exact nonnegative_of_acceptCheck
          terms sqrtFuel logFuel haccept hpoint)
      (by
        intro box data hdiscard
        simp [noDiscard] at hdiscard)
      checked coordinate hcoordinate trivial
    exact hconditional hinterior

/-! ## Target-loss default and historical relative-width diagnostic -/

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

/-- The centered rule encloses the full `h` interval directly.  Its value
radius is therefore the target-scale uncertainty removable by splitting
`h`, without requesting a potentially singular `h` derivative. -/
def splitScoreChi (box : CertificateBox)
    (evaluation : MidpointSKCertificate) : ℚ :=
  if box.chiLo < box.chiHi then
    RationalEnclosure.radius evaluation.value
  else
    0

/-- Deterministic positive-width fallback used only if all target-loss
scores vanish. -/
def widestAxis (box : CertificateBox) : CertificateAxis :=
  let ws := RationalEnclosure.radius box.sInterval
  let wk := RationalEnclosure.radius box.kInterval
  let wh := RationalEnclosure.radius box.chiInterval
  if ws ≥ wk ∧ ws ≥ wh ∧ box.sLo < box.sHi then .s
  else if wk ≥ wh ∧ box.kLo < box.kHi then .k
  else if box.chiLo < box.chiHi then .chi
  else if box.sLo < box.sHi then .s
  else .k

/-- Default first-bracket splitter.  The sharp centered evaluation is bound
once, and the largest removable target-scale loss is selected with tie order
`s`, then `K`, then `h`. -/
def chooseTargetAxis (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : CertificateAxis :=
  let evaluation := evaluateSharpCentered terms box
    (autoCentered sqrtFuel logFuel box)
  let ss := splitScoreS box evaluation
  let sk := splitScoreK box evaluation
  let sc := splitScoreChi box evaluation
  if ss = 0 ∧ sk = 0 ∧ sc = 0 then widestAxis box
  else if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
  else if sk ≥ sc ∧ box.kLo < box.kHi then .k
  else if box.chiLo < box.chiHi then .chi
  else if box.sLo < box.sHi then .s
  else .k

/-- The historical splitter compares the relative widths of `s` and `K`
with the absolute width of `h`, using exact cross-products.  Ties are ordered
`s`, then `K`, then `h`; endpoint guards never choose a zero-width axis while
another coordinate remains splittable.  It is retained for topology
comparison and diagnostics; `buildTree` uses `chooseTargetAxis`. -/
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

/-- Build only compact hybrid tags and midpoint split axes. -/
def buildTree (terms sqrtFuel logFuel : ℕ) :
    ℕ → CertificateBox → Option Tree
  | 0, box =>
      match autoAccept terms sqrtFuel logFuel box with
      | some tag => some (.accept tag)
      | none => none
  | fuel + 1, box =>
      match autoAccept terms sqrtFuel logFuel box with
      | some tag => some (.accept tag)
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
              | some upper => some (.split axis lower upper)

/-- A successful untrusted build passes the ordinary compact checker. -/
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
      | none =>
          simp [buildTree, haccept] at hbuild
      | some tag =>
          simp [buildTree, haccept] at hbuild
          subst tree
          simpa [Tree.check] using
            autoAccept_check_of_eq
              terms sqrtFuel logFuel box tag haccept
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
          let axis := chooseTargetAxis terms sqrtFuel logFuel box
          let cut := axisCut box axis
          generalize hlower :
            buildTree terms sqrtFuel logFuel fuel
              (box.lower axis cut) = lowerOption
          cases lowerOption with
          | none =>
              simp [buildTree, haccept, axis, cut, hlower] at hbuild
          | some lower =>
              generalize hupper :
                buildTree terms sqrtFuel logFuel fuel
                  (box.upper axis cut) = upperOption
              cases upperOption with
              | none =>
                  simp [buildTree, haccept, axis, cut,
                    hlower, hupper] at hbuild
              | some upper =>
                  simp [buildTree, haccept, axis, cut,
                    hlower, hupper] at hbuild
                  subst tree
                  simp only [Tree.check, Bool.and_eq_true]
                  exact ⟨ih _ _ hlower, ih _ _ hupper⟩

/-! ## Compact checked trees -/

/-- A compact hybrid topology together with its ordinary Boolean replay. -/
structure AutoTaggedCheckedTree
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  certificate : Tree
  checked : certificate.check terms sqrtFuel logFuel root = true

namespace AutoTaggedCheckedTree

/-- Convert one compact checked tree to the first-bracket semantic boundary. -/
def toFirstBracketTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : AutoTaggedCheckedTree terms sqrtFuel logFuel root) :
    FirstBracketTree root :=
  firstBracketTreeOfCheckedCertificate terms sqrtFuel logFuel
    (materialize root tree.certificate) (by
      rw [materialize_check]
      exact tree.checked)

/-- Package any successfully built compact topology. -/
def ofBuildTreeEq
    {terms sqrtFuel logFuel fuel : ℕ} {root : CertificateBox}
    (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel root = some tree) :
    AutoTaggedCheckedTree terms sqrtFuel logFuel root where
  certificate := tree
  checked := buildTree_check_of_eq
    terms sqrtFuel logFuel fuel root tree hbuild

end AutoTaggedCheckedTree

/-! ## Fixed ten-slab forest -/

/-- Ten midpoint trees for the fixed dyadic `s` slabs of one historical
`K` band.  All slabs share one evaluator parameter triple. -/
structure TenSlabForest
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  slab0 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab0Root root)
  slab1 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab1Root root)
  slab2 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab2Root root)
  slab3 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab3Root root)
  slab4 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab4Root root)
  slab5 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab5Root root)
  slab6 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab6Root root)
  slab7 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab7Root root)
  slab8 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab8Root root)
  slab9 : AutoTaggedCheckedTree terms sqrtFuel logFuel
    (firstBracketSlab9Root root)

namespace TenSlabForest

/-- Materialize each compact slab independently, then join the ten fixed
dyadic roots by their nine explicit historical cuts. -/
def certificate
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    SubdivisionCertificate AcceptTag Unit :=
  .split .s firstBracketSCut0
    (materialize (firstBracketSlab0Root root)
      forest.slab0.certificate)
    (.split .s firstBracketSCut1
      (materialize (firstBracketSlab1Root root)
        forest.slab1.certificate)
      (.split .s firstBracketSCut2
        (materialize (firstBracketSlab2Root root)
          forest.slab2.certificate)
        (.split .s firstBracketSCut3
          (materialize (firstBracketSlab3Root root)
            forest.slab3.certificate)
          (.split .s firstBracketSCut4
            (materialize (firstBracketSlab4Root root)
              forest.slab4.certificate)
            (.split .s firstBracketSCut5
              (materialize (firstBracketSlab5Root root)
                forest.slab5.certificate)
              (.split .s firstBracketSCut6
                (materialize (firstBracketSlab6Root root)
                  forest.slab6.certificate)
                (.split .s firstBracketSCut7
                  (materialize (firstBracketSlab7Root root)
                    forest.slab7.certificate)
                  (.split .s firstBracketSCut8
                    (materialize (firstBracketSlab8Root root)
                      forest.slab8.certificate)
                    (materialize (firstBracketSlab9Root root)
                      forest.slab9.certificate)))))))))

/-- The aggregate proof unfolds only the fixed split skeleton and checker
commutation, then combines the ten opaque slab checks. -/
theorem certificate_check
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    (certificate forest).check
      (acceptCheck terms sqrtFuel logFuel) noDiscard root = true := by
  simp only [certificate, SubdivisionCertificate.check, Bool.and_eq_true,
    materialize_check]
  exact
    ⟨forest.slab0.checked,
      ⟨forest.slab1.checked,
        ⟨forest.slab2.checked,
          ⟨forest.slab3.checked,
            ⟨forest.slab4.checked,
              ⟨forest.slab5.checked,
                ⟨forest.slab6.checked,
                  ⟨forest.slab7.checked,
                    ⟨forest.slab8.checked, forest.slab9.checked⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- A checked fixed-slab forest supplies the aggregate first-bracket tree. -/
def toFirstBracketTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    FirstBracketTree root :=
  firstBracketTreeOfCheckedCertificate terms sqrtFuel logFuel
    (certificate forest) (certificate_check forest)

end TenSlabForest

end LRDeterminantLowRatioFiniteVFirstBracketAutoTree

end CourtadeKumar
