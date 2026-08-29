import InformationTheory.CourtadeKumar.LRDeterminantRestrictedCoreAssembly
import InformationTheory.CourtadeKumar.LRDeterminantIdealCoarseCertificate
import Mathlib.Data.Rat.Sqrt

/-!
# Hybrid automatic tree for the restricted deep ideal band

This module checks the ideal-core inequality on the exact parameter range

* `L >= lrDeterminantIdealDeepL0`,
* `1 <= k <= 4`,
* `0 <= chi <= 1`, and
* margin `3/5`.

An accepted leaf stores only whether to use the direct endpoint checker or
the coarse global-`L` checker.  Both reconstruct their verified interval
payload from the current box.  Generator output remains untrusted: it must
pass the independent `Tree.check` replay before it can be packaged as a
`CheckedTree`.  The theorem `idealOneToFour_of_checkedTree` then supplies
the exact proposition required by the restricted determinant assembly.
-/

namespace CourtadeKumar
namespace LRDeterminantIdealOneToFourHybridAutoTree

/-! ## Compact hybrid leaves -/

inductive AcceptTag where
  | direct
  | coarse
  deriving DecidableEq, Repr

def acceptCheck (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) : AcceptTag → Bool
  | .direct =>
      LRDeterminantIdealEvaluatorCertificate.autoAccepts
        terms logFuel margin box ()
  | .coarse =>
      LRDeterminantIdealCoarseEvaluator.autoAccepts
        terms logFuel margin box ()

def autoAccept (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) : Option AcceptTag :=
  if LRDeterminantIdealEvaluatorCertificate.autoAccepts
      terms logFuel margin box () then
    some .direct
  else if LRDeterminantIdealCoarseEvaluator.autoAccepts
      terms logFuel margin box () then
    some .coarse
  else
    none

theorem autoAccept_check_of_eq
    (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) (tag : AcceptTag)
    (hauto : autoAccept terms logFuel margin box = some tag) :
    acceptCheck terms logFuel margin box tag = true := by
  unfold autoAccept at hauto
  split at hauto <;> rename_i hdirect
  · cases hauto
    simpa [acceptCheck] using hdirect
  split at hauto <;> rename_i hcoarse
  · cases hauto
    simpa [acceptCheck] using hcoarse
  · simp at hauto

theorem idealCore_gt_of_acceptCheck
    (terms logFuel : ℕ) (margin : ℚ)
    {L : ℝ} (hL : lrDeterminantIdealDeepL0 ≤ L)
    {box : CertificateBox} {tag : AcceptTag}
    (haccept : acceptCheck terms logFuel margin box tag = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (margin : ℝ) < lrDeterminantIdealCore L point.k point.chi := by
  cases tag with
  | direct =>
      have hendpoint :=
        LRDeterminantIdealEvaluatorCertificate.autoAccepts_sound
          terms logFuel margin box () (by
            simpa [acceptCheck] using haccept) point hpoint
      exact lrDeterminantIdealCore_gt_of_endpointProperties
        lrDeterminantIdealDeepL0_add_C_pos hL hendpoint
  | coarse =>
      have hcoarse := LRDeterminantIdealCoarseEvaluator.autoAccepts_sound
        terms logFuel margin box () (by
          simpa [acceptCheck] using haccept) point hpoint
      exact lrDeterminantIdealCore_gt_of_coarseProperties hL hcoarse

/-! ## Compact midpoint topology -/

/-- Use the exact geometric `k` midpoint whenever the product of the two
endpoints is a rational square, and the ordinary exact rational midpoint
otherwise.  This is the mirror policy that cuts `[1,4]` at `2`. -/
def logarithmicKCut (box : CertificateBox) : ℚ :=
  let product := box.kLo * box.kHi
  let candidate := Rat.sqrt product
  if candidate * candidate = product ∧
      box.kLo < candidate ∧ candidate < box.kHi then
    candidate
  else
    RationalEnclosure.center box.kInterval

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => logarithmicKCut box
  | .chi => RationalEnclosure.center box.chiInterval

inductive Tree where
  | accept (tag : AcceptTag)
  | split (axis : CertificateAxis) (lower upper : Tree)
  deriving Repr

namespace Tree

def check (terms logFuel : ℕ) (margin : ℚ) :
    Tree → CertificateBox → Bool
  | .accept tag, box => acceptCheck terms logFuel margin box tag
  | .split axis lower upper, box =>
      let cut := axisCut box axis
      check terms logFuel margin lower (box.lower axis cut) &&
        check terms logFuel margin upper (box.upper axis cut)

def nodeCount : Tree → ℕ
  | .accept _ => 1
  | .split _ lower upper => 1 + nodeCount lower + nodeCount upper

def leafCount : Tree → ℕ
  | .accept _ => 1
  | .split _ lower upper => leafCount lower + leafCount upper

def directLeafCount : Tree → ℕ
  | .accept .direct => 1
  | .accept .coarse => 0
  | .split _ lower upper => directLeafCount lower + directLeafCount upper

def coarseLeafCount : Tree → ℕ
  | .accept .direct => 0
  | .accept .coarse => 1
  | .split _ lower upper => coarseLeafCount lower + coarseLeafCount upper

def maxDepth : Tree → ℕ
  | .accept _ => 0
  | .split _ lower upper => 1 + max (maxDepth lower) (maxDepth upper)

def axisToken : CertificateAxis → Char
  | .s => 's'
  | .k => 'k'
  | .chi => 'h'

/-- One-byte preorder serialization using `D`/`C` leaves and `s`/`k`/`h` splits. -/
def tokens : Tree → List Char
  | .accept .direct => ['D']
  | .accept .coarse => ['C']
  | .split axis lower upper =>
      axisToken axis :: (tokens lower ++ tokens upper)

def packed (tree : Tree) : String := String.ofList tree.tokens

end Tree

/-! ## Structural soundness and the exact requested theorem -/

theorem idealCore_gt_of_check
    (terms logFuel : ℕ) (margin : ℚ)
    {L : ℝ} (hL : lrDeterminantIdealDeepL0 ≤ L)
    {box : CertificateBox} {tree : Tree}
    (hcheck : tree.check terms logFuel margin box = true) :
    ∀ point, box.Contains point →
      (margin : ℝ) < lrDeterminantIdealCore L point.k point.chi := by
  induction tree generalizing box with
  | accept tag =>
      intro point hpoint
      exact idealCore_gt_of_acceptCheck terms logFuel margin hL
        (by simpa [Tree.check] using hcheck) hpoint
  | split axis lower upper lower_ih upper_ih =>
      have hparts :
          lower.check terms logFuel margin
                (box.lower axis (axisCut box axis)) = true ∧
            upper.check terms logFuel margin
                (box.upper axis (axisCut box axis)) = true := by
        simpa [Tree.check, Bool.and_eq_true] using hcheck
      intro point hpoint
      rcases box.contains_lower_or_upper hpoint axis (axisCut box axis) with
        hlower | hupper
      · exact lower_ih hparts.1 point hlower
      · exact upper_ih hparts.2 point hupper

def rootBox : CertificateBox :=
  { sLo := 0, sHi := 1 / 128
    kLo := 1, kHi := 4
    chiLo := 0, chiHi := 1 }

structure CheckedTree (terms logFuel : ℕ) (margin : ℚ) where
  certificate : Tree
  checked : certificate.check terms logFuel margin rootBox = true

/-- The exact adapter consumed by `LRDeterminantRestrictedCoreAssembly`.
The dummy `s=0` coordinate only embeds `(k,chi)` into the common box type;
the ideal evaluator and target are independent of it. -/
def idealOneToFour_of_checkedTree
    {terms logFuel : ℕ} {margin : ℚ}
    (hmargin : margin = 3 / 5)
    (tree : CheckedTree terms logFuel margin) :
    LRDeterminantIdealOneToFourTheorem := by
  subst margin
  intro L hL k chi hk hchi
  let point : CertificatePoint := { s := 0, k := k, chi := chi }
  have hpoint : rootBox.Contains point := by
    rcases hk with ⟨hkLower, hkUpper⟩
    rcases hchi with ⟨hchiLower, hchiUpper⟩
    simpa [rootBox, point, CertificateBox.Contains] using
      (show (0 : ℝ) ≤ 0 ∧ 0 ≤ (1 / 128 : ℝ) ∧
          1 ≤ k ∧ k ≤ 4 ∧ 0 ≤ chi ∧ chi ≤ 1 from
        ⟨by norm_num, by norm_num, hkLower, hkUpper,
          hchiLower, hchiUpper⟩)
  simpa [point] using
    (idealCore_gt_of_check terms logFuel (3 / 5) hL
      tree.checked point hpoint)

/-! ## Untrusted deterministic generator -/

/-- A shared-payload estimate of the best direct/coarse reserve.  This is
used only to choose a split and has no proof authority. -/
def hybridSlack (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) : ℚ :=
  let payload := LRDeterminantIdealEvaluatorCertificate.auto logFuel box
  if payload.payloadCheck terms box then
    let direct := payload.evaluate terms box
    let coarse := LRDeterminantIdealCoarseEvaluator.evaluate
      terms box payload
    let directSlack := min (direct.core.lower - margin)
      (min direct.derivative.lower direct.c1.lower)
    let coarseSlack := min (coarse.core.lower - margin)
      (min coarse.derivative.lower coarse.c1.lower)
    max directSlack coarseSlack
  else
    -1000000

def splitScore (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) (axis : CertificateAxis) : ℚ :=
  let cut := axisCut box axis
  min (hybridSlack terms logFuel margin (box.lower axis cut))
    (hybridSlack terms logFuel margin (box.upper axis cut))

/-- Exact-rational version of the successful mirror policy: first isolate
the zero-touching quarter strip, then compare relative `k` width with
absolute `chi` width, and otherwise maximize the worst child slack. -/
def chooseAxis (terms logFuel : ℕ) (margin : ℚ)
    (box : CertificateBox) : CertificateAxis :=
  let canK := box.kLo < box.kHi
  let canChi := box.chiLo < box.chiHi
  let dk := box.kHi - box.kLo
  let dchi := box.chiHi - box.chiLo
  if box.chiLo = 0 ∧ 1 / 4 < box.chiHi then .chi
  else if canK ∧ canChi ∧ dk ≤ dchi * box.kLo then .chi
  else if canK ∧ canChi then
    if splitScore terms logFuel margin box .k ≥
        splitScore terms logFuel margin box .chi then .k else .chi
  else if canK then .k
  else .chi

def buildTree (terms logFuel : ℕ) (margin : ℚ) :
    ℕ → CertificateBox → Option Tree
  | 0, box =>
      match autoAccept terms logFuel margin box with
      | some tag => some (.accept tag)
      | none => none
  | fuel + 1, box =>
      match autoAccept terms logFuel margin box with
      | some tag => some (.accept tag)
      | none =>
          let axis := chooseAxis terms logFuel margin box
          let cut := axisCut box axis
          match buildTree terms logFuel margin fuel
              (box.lower axis cut) with
          | none => none
          | some lower =>
              match buildTree terms logFuel margin fuel
                  (box.upper axis cut) with
              | none => none
              | some upper => some (.split axis lower upper)

/-- Interval-evaluator truncation used by the deterministic candidate generator. -/
def generatorTerms : ℕ := 8

/-- Exact-log reduction fuel used by the deterministic candidate generator. -/
def generatorLogFuel : ℕ := 7

/-- Target margin used by the deterministic candidate generator. -/
def generatorMargin : ℚ := 3 / 5

/-- Subdivision depth available to the deterministic candidate generator. -/
def generatorFuel : ℕ := 22

/-- Pure deterministic candidate generation.  The returned topology has no
proof authority until it passes `Tree.check` and is packaged as a
`CheckedTree`. -/
def generate : Option Tree :=
  buildTree generatorTerms generatorLogFuel generatorMargin generatorFuel rootBox

end LRDeterminantIdealOneToFourHybridAutoTree
end CourtadeKumar
