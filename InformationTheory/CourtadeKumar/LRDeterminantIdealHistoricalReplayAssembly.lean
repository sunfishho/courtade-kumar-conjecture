import InformationTheory.CourtadeKumar.LRDeterminantIdealMeanValuePackedCertificate
import InformationTheory.CourtadeKumar.LRDeterminantIdealCenteredMeanOracle
import InformationTheory.CourtadeKumar.LRDeterminantIdealHistoricalTopologyData

/-!
# Assembly for the exact historical ideal forests

The audited low-`k` topology has four independently rooted components:

* the middle target on `k in [1/32, 5/32]`;
* the upper target on `k in [5/32, 1/4]`;
* the upper target on `k in [1/4, 1/2]`; and
* the upper target on `k in [1/2, 1]`.

The last three components cannot be combined by inserting ordinary packed
`k` tokens above them: those tokens always split at the arithmetic midpoint,
whereas the historical outer cuts are exactly `1/4` and `1/2`.  This module
therefore performs those two joins at theorem level.  The restricted
`L0 = 14 * log 2` forest similarly retains its two exact roots `[1,2]` and
`[2,4]`, using the already-verified theorem-level adapter at `k = 2`.

Concrete packed strings are deliberately kept in a separate generated data
module.  Whole-root packed replay is the preferred first pass.  If a root is
too expensive to reduce monolithically, it may instead be proved as several
`CheckedChunk`s at exact midpoint paths and joined before being supplied to
the checked-forest interfaces below; no theorem-facing change is required.
-/

namespace CourtadeKumar
namespace LRIdealHistoricalReplayAssembly

open LRLowKIdealMeanValue
open LRLowKIdealMeanValuePackedCertificate
open LRIdealCenteredMeanOracle
open LRIdealHistoricalTopologyData

/-! ## The three exact historical upper-target roots -/

def lowKUpperFiveThirtySecondsToQuarterRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 5 / 32, kHi := 1 / 4
    chiLo := 0, chiHi := 1 }

def lowKUpperQuarterToHalfRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 1 / 4, kHi := 1 / 2
    chiLo := 0, chiHi := 1 }

def lowKUpperHalfToOneRoot : CertificateBox :=
  { sLo := 0, sHi := 0
    kLo := 1 / 2, kHi := 1
    chiLo := 0, chiHi := 1 }

/-! ## Path-preserving chunk joins -/

/-- Following an appended path is the same as following the first path and
then the second.  This lets generated chunks record their full root-relative
paths while structural joins continue to use the semantic midpoint checker. -/
theorem follow_append (box : CertificateBox) (left right : Path) :
    follow box (left ++ right) = follow (follow box left) right := by
  induction left generalizing box with
  | nil => rfl
  | cons step rest ih =>
      simpa [follow] using ih (descend box step)

/-- The singleton specialization used at every generated internal node. -/
theorem follow_append_singleton
    (box : CertificateBox) (path : Path) (step : Step) :
    follow box (path ++ [step]) = descend (follow box path) step := by
  simpa [follow] using follow_append box path [step]

/-- Join two independently checked chunks whose paths are the lower and upper
extensions of the same exact midpoint node. -/
noncomputable def joinAtPath
    {targets : TargetTriple} {oracle : AutoOracle targets}
    (root : CertificateBox) (path : Path) (axis : CertificateAxis)
    (lower : CheckedChunk oracle
      (follow root (path ++ [{ axis := axis, branch := .lower }])))
    (upper : CheckedChunk oracle
      (follow root (path ++ [{ axis := axis, branch := .upper }]))) :
    CheckedChunk oracle (follow root path) := by
  apply join axis
  · simpa [follow_append_singleton, descend] using lower
  · simpa [follow_append_singleton, descend] using upper

/-! ## Four-component low-`k` theorem adapter -/

/-- The exact historical four-component forest, after each component has
been independently checked by the semantic natural/mean oracle. -/
structure LowKHistoricalCheckedForest
    (middleOracle : AutoOracle middleTargets)
    (upperOracle : AutoOracle upperTargets) where
  middle : CheckedTree middleOracle middleRoot
  upperFiveThirtySecondsToQuarter :
    CheckedTree upperOracle lowKUpperFiveThirtySecondsToQuarterRoot
  upperQuarterToHalf :
    CheckedTree upperOracle lowKUpperQuarterToHalfRoot
  upperHalfToOne : CheckedTree upperOracle lowKUpperHalfToOneRoot

/-- The four historical components discharge the exact remaining
`LRLowKIdealReplayCertificate`.  The middle component is used directly.  The
upper theorem is assembled by exact case splits at `k = 1/4` and `k = 1/2`,
not by pretending that those are midpoints of `[5/32,1]`. -/
noncomputable def lowKIdealReplayCertificate_of_historicalCheckedForest
    (middleOracle : AutoOracle middleTargets)
    (upperOracle : AutoOracle upperTargets)
    (forest : LowKHistoricalCheckedForest middleOracle upperOracle) :
    LRLowKIdealReplayCertificate := by
  apply lrLowKIdealReplayCertificate_of_middle_upper
  · intro k chi hk hchi
    let point : CertificatePoint := { s := 0, k := k, chi := chi }
    have hpoint : middleRoot.Contains point := by
      rcases hk with ⟨hkLower, hkUpper⟩
      rcases hchi with ⟨hchiLower, hchiUpper⟩
      simpa [middleRoot, point, CertificateBox.Contains] using
        (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
            1 / 32 ≤ k ∧ k ≤ 5 / 32 ∧
            0 ≤ chi ∧ chi ≤ 1 from
          ⟨by norm_num, by norm_num, hkLower, hkUpper,
            hchiLower, hchiUpper⟩)
    have hpositive := positiveAt_of_treeCheck middleOracle
      forest.middle.checked point hpoint
    simpa [point] using (middle_positive_iff_legacy point).mp hpositive
  · intro k chi hk hchi
    let point : CertificatePoint := { s := 0, k := k, chi := chi }
    by_cases hkQuarter : k ≤ 1 / 4
    · have hpoint : lowKUpperFiveThirtySecondsToQuarterRoot.Contains point := by
        rcases hk with ⟨hkLower, _hkUpper⟩
        rcases hchi with ⟨hchiLower, hchiUpper⟩
        simpa [lowKUpperFiveThirtySecondsToQuarterRoot, point,
          CertificateBox.Contains] using
          (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
              5 / 32 ≤ k ∧ k ≤ 1 / 4 ∧
              0 ≤ chi ∧ chi ≤ 1 from
            ⟨by norm_num, by norm_num, hkLower, hkQuarter,
              hchiLower, hchiUpper⟩)
      have hpositive := positiveAt_of_treeCheck upperOracle
        forest.upperFiveThirtySecondsToQuarter.checked point hpoint
      simpa [point] using (upper_positive_iff_legacy point).mp hpositive
    · have hkQuarterLower : 1 / 4 ≤ k :=
        le_of_lt (lt_of_not_ge hkQuarter)
      by_cases hkHalf : k ≤ 1 / 2
      · have hpoint : lowKUpperQuarterToHalfRoot.Contains point := by
          rcases hchi with ⟨hchiLower, hchiUpper⟩
          simpa [lowKUpperQuarterToHalfRoot, point,
            CertificateBox.Contains] using
            (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
                1 / 4 ≤ k ∧ k ≤ 1 / 2 ∧
                0 ≤ chi ∧ chi ≤ 1 from
              ⟨by norm_num, by norm_num, hkQuarterLower, hkHalf,
                hchiLower, hchiUpper⟩)
        have hpositive := positiveAt_of_treeCheck upperOracle
          forest.upperQuarterToHalf.checked point hpoint
        simpa [point] using (upper_positive_iff_legacy point).mp hpositive
      · have hkHalfLower : 1 / 2 ≤ k :=
          le_of_lt (lt_of_not_ge hkHalf)
        have hpoint : lowKUpperHalfToOneRoot.Contains point := by
          rcases hk with ⟨_hkLower, hkUpper⟩
          rcases hchi with ⟨hchiLower, hchiUpper⟩
          simpa [lowKUpperHalfToOneRoot, point,
            CertificateBox.Contains] using
            (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 0 ∧
                1 / 2 ≤ k ∧ k ≤ 1 ∧
                0 ≤ chi ∧ chi ≤ 1 from
              ⟨by norm_num, by norm_num, hkHalfLower, hkUpper,
                hchiLower, hchiUpper⟩)
        have hpositive := positiveAt_of_treeCheck upperOracle
          forest.upperHalfToOne.checked point hpoint
        simpa [point] using (upper_positive_iff_legacy point).mp hpositive

/-! ## Packed convenience interfaces -/

/-- Whole-root packed data for the exact four-component low-`k` forest.
The more general checked interface above also accepts a forest assembled from
smaller midpoint-rooted chunks. -/
structure LowKHistoricalPackedForest
    (middleOracle : AutoOracle middleTargets)
    (upperOracle : AutoOracle upperTargets) where
  middle : PackedCheckedTree middleOracle middleRoot
  upperFiveThirtySecondsToQuarter :
    PackedCheckedTree upperOracle lowKUpperFiveThirtySecondsToQuarterRoot
  upperQuarterToHalf :
    PackedCheckedTree upperOracle lowKUpperQuarterToHalfRoot
  upperHalfToOne : PackedCheckedTree upperOracle lowKUpperHalfToOneRoot

namespace LowKHistoricalPackedForest

noncomputable def toCheckedForest
    {middleOracle : AutoOracle middleTargets}
    {upperOracle : AutoOracle upperTargets}
    (forest : LowKHistoricalPackedForest middleOracle upperOracle) :
    LowKHistoricalCheckedForest middleOracle upperOracle where
  middle := forest.middle.toCheckedTree
  upperFiveThirtySecondsToQuarter :=
    forest.upperFiveThirtySecondsToQuarter.toCheckedTree
  upperQuarterToHalf := forest.upperQuarterToHalf.toCheckedTree
  upperHalfToOne := forest.upperHalfToOne.toCheckedTree

noncomputable def toReplayCertificate
    {middleOracle : AutoOracle middleTargets}
    {upperOracle : AutoOracle upperTargets}
    (forest : LowKHistoricalPackedForest middleOracle upperOracle) :
    LRLowKIdealReplayCertificate :=
  lowKIdealReplayCertificate_of_historicalCheckedForest
    middleOracle upperOracle forest.toCheckedForest

end LowKHistoricalPackedForest

/-- The two exact restricted components after independent semantic replay. -/
structure RestrictedHistoricalCheckedForest
    (oracle : AutoOracle restrictedTargets) where
  lower : CheckedTree oracle restrictedLowerRoot
  upper : CheckedTree oracle restrictedUpperRoot

namespace RestrictedHistoricalCheckedForest

noncomputable def toIdealTheorem
    {oracle : AutoOracle restrictedTargets}
    (forest : RestrictedHistoricalCheckedForest oracle) :
    LRDeterminantIdealOneToFourTheorem :=
  idealOneToFour_of_twoCheckedTrees oracle forest.lower forest.upper

end RestrictedHistoricalCheckedForest

/-- Whole-root packed data for the exact two-component restricted forest. -/
structure RestrictedHistoricalPackedForest
    (oracle : AutoOracle restrictedTargets) where
  lower : PackedCheckedTree oracle restrictedLowerRoot
  upper : PackedCheckedTree oracle restrictedUpperRoot

namespace RestrictedHistoricalPackedForest

noncomputable def toIdealTheorem
    {oracle : AutoOracle restrictedTargets}
    (forest : RestrictedHistoricalPackedForest oracle) :
    LRDeterminantIdealOneToFourTheorem :=
  (show RestrictedHistoricalCheckedForest oracle from {
    lower := forest.lower.toCheckedTree
    upper := forest.upper.toCheckedTree }).toIdealTheorem

end RestrictedHistoricalPackedForest

/-! ## Exact generated strings and their six independent replay checks -/

/-- The four whole-root Boolean checks for the generated low-`k` streams.
This is merely a convenient batching record: each field is an ordinary
kernel-reduced equality for `packedCheck`.  If one field is too expensive as
a monolithic reduction, the corresponding theorem may instead be supplied
through `LowKHistoricalCheckedForest` after chunking that one component. -/
structure LowKHistoricalWholeRootChecks (terms logFuel : ℕ) : Prop where
  l7Middle :
    packedCheck (middleAutoOracle terms logFuel) middleRoot
      l7MiddlePacked = true
  l7UpperFiveThirtySecondsToQuarter :
    packedCheck (upperAutoOracle terms logFuel)
      lowKUpperFiveThirtySecondsToQuarterRoot
      l7UpperFiveThirtySecondsToQuarterPacked = true
  l7UpperQuarterToHalf :
    packedCheck (upperAutoOracle terms logFuel)
      lowKUpperQuarterToHalfRoot l7UpperQuarterToHalfPacked = true
  l7UpperHalfToOne :
    packedCheck (upperAutoOracle terms logFuel)
      lowKUpperHalfToOneRoot l7UpperHalfToOnePacked = true

/-- The two whole-root Boolean checks for the generated restricted streams.
Their checker parameters are independent of the low-`k` parameters, so each
forest may use the cheapest pair that its exact replay accepts. -/
structure RestrictedHistoricalWholeRootChecks (terms logFuel : ℕ) : Prop where
  l14Lower :
    packedCheck (restrictedAutoOracle terms logFuel) restrictedLowerRoot
      l14LowerPacked = true
  l14Upper :
    packedCheck (restrictedAutoOracle terms logFuel) restrictedUpperRoot
      l14UpperPacked = true

/-- Materialize the four low-`k` packed roots from their independent Boolean
checks. -/
noncomputable def lowKHistoricalPackedForestOfChecks
    {terms logFuel : ℕ}
    (checks : LowKHistoricalWholeRootChecks terms logFuel) :
    LowKHistoricalPackedForest
      (middleAutoOracle terms logFuel) (upperAutoOracle terms logFuel) where
  middle := {
    packed := l7MiddlePacked
    checked := checks.l7Middle }
  upperFiveThirtySecondsToQuarter := {
    packed := l7UpperFiveThirtySecondsToQuarterPacked
    checked := checks.l7UpperFiveThirtySecondsToQuarter }
  upperQuarterToHalf := {
    packed := l7UpperQuarterToHalfPacked
    checked := checks.l7UpperQuarterToHalf }
  upperHalfToOne := {
    packed := l7UpperHalfToOnePacked
    checked := checks.l7UpperHalfToOne }

/-- Materialize the two restricted packed roots from their independent
Boolean checks. -/
noncomputable def restrictedHistoricalPackedForestOfChecks
    {terms logFuel : ℕ}
    (checks : RestrictedHistoricalWholeRootChecks terms logFuel) :
    RestrictedHistoricalPackedForest
      (restrictedAutoOracle terms logFuel) where
  lower := {
    packed := l14LowerPacked
    checked := checks.l14Lower }
  upper := {
    packed := l14UpperPacked
    checked := checks.l14Upper }

/-- Preferred whole-root path from the generated `L0 = 7 * log 2` streams to
the exact low-`k` replay certificate. -/
noncomputable def lowKIdealReplayCertificate_of_historicalWholeRootChecks
    {terms logFuel : ℕ}
    (checks : LowKHistoricalWholeRootChecks terms logFuel) :
    LRLowKIdealReplayCertificate :=
  (lowKHistoricalPackedForestOfChecks checks).toReplayCertificate

/-- Preferred whole-root path from the generated `L0 = 14 * log 2` streams
to the exact restricted ideal theorem. -/
noncomputable def idealOneToFour_of_historicalWholeRootChecks
    {terms logFuel : ℕ}
    (checks : RestrictedHistoricalWholeRootChecks terms logFuel) :
    LRDeterminantIdealOneToFourTheorem :=
  (restrictedHistoricalPackedForestOfChecks checks).toIdealTheorem

/-!
The concrete replay-data module should instantiate the two structures above
with `LRIdealCenteredMeanOracle.middleAutoOracle`, `upperAutoOracle`, and
`restrictedAutoOracle`.  After the six Boolean checks have been discharged,
the intended final closed theorem names are:

* `lrLowKIdealReplayCertificate_historicalMeanValue_proved`;
* `lrDeterminantIdealOneToFour_historicalMeanValue_proved`.

Those names are reserved for the concrete data/reduction module rather than
declared here behind assumptions.
-/

end LRIdealHistoricalReplayAssembly
end CourtadeKumar
