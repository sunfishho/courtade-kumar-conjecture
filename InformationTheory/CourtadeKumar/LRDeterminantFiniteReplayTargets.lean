import InformationTheory.CourtadeKumar.LRDeterminantFiniteRegions

/-!
# Exact replay targets for the finite determinant ledger

The raw finite suites do not directly enclose the unscaled singular
determinant.  Their exact D9 target is

`N1 = 3*s*Hd*FirstBracket + 4*R*W*T*(B*x-D1)`.

The upper-`K` suite uses the different target `FirstBracket/e`.  This module
records those exact targets, proves the positive-factor adapters to the two
admitted determinant formats, and gives checked-tree packages with the
correct target types.

In particular, a raw replay must explicitly supply a proof that its concrete
discard checker excludes `LRHighShapeVRelevant` points.  No compatibility
between historical replay data and the existing Lean discard datatype is
asserted here without that proof.
-/

namespace CourtadeKumar

/-! ## Exact replay targets and their sign adapters -/

/-- Formula (D9), exactly as enclosed by each of the six raw determinant
suites. -/
noncomputable def lrFiniteDeterminantD9ReplayTarget
    (point : CertificatePoint) : ℝ :=
  3 * point.s * lrDeterminantHd point *
      lrDeterminantFirstBracket
        (lrCertificateBFlow point) (lrDeterminantD1 point)
        (lrCertificateGShape point) (lrDeterminantPsi point)
        (lrDeterminantDelta point) (lrCertificateW point) +
    4 * lrCertificateR point * lrCertificateW point *
      lrDeterminantT point *
        (lrCertificateBFlow point * lrCertificateX point -
          lrDeterminantD1 point)

/-- Exact target of the upper-`K` replay: the first bracket divided by the
positive chart variable `e = s*k`. -/
noncomputable def lrFiniteDeterminantUpperKReplayTarget
    (point : CertificatePoint) : ℝ :=
  lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point) /
    lrCertificateE point

/-- D9 is exactly `3*s*Hd` times the cleared singular determinant.  This is
the certificate-coordinate specialization of the scaled identity (D5). -/
theorem lrFiniteDeterminantD9ReplayTarget_eq_scaledCleared
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrFiniteDeterminantD9ReplayTarget point =
      3 * point.s * lrDeterminantHd point *
        lrDeterminantClearedSingular
          (lrCertificateBFlow point) (lrDeterminantD1 point)
          (lrCertificateGShape point) (lrDeterminantPsi point)
          (lrDeterminantDelta point) (lrCertificateW point)
          (lrDeterminantC0 point) (lrCertificateX point)
          (lrDeterminantT point) := by
  have hscaled := lrDeterminantClearedSingular_scaled_firstBracket
    (B := lrCertificateBFlow point)
    (D1 := lrDeterminantD1 point)
    (G := lrCertificateGShape point)
    (psi := lrDeterminantPsi point)
    (delta := lrDeterminantDelta point)
    (W := lrCertificateW point)
    (c0 := lrDeterminantC0 point)
    (x := lrCertificateX point)
    (T := lrDeterminantT point)
    (R := lrCertificateR point)
    (s := point.s)
    (H := lrDeterminantHd point)
    hinterior.1.1.ne' (lrDeterminantHd_pos hinterior).ne'
    (by rfl)
  simpa [lrFiniteDeterminantD9ReplayTarget] using hscaled.symm

/-- A nonnegative exact D9 replay target yields the admitted cleared-singular
target after cancelling the strictly positive factor `3*s*Hd`. -/
theorem lrDeterminantAdmittedTarget_of_D9ReplayTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hD9 : 0 ≤ lrFiniteDeterminantD9ReplayTarget point) :
    LRDeterminantAdmittedTarget point := by
  rw [lrFiniteDeterminantD9ReplayTarget_eq_scaledCleared hinterior] at hD9
  have hscale : 0 < 3 * point.s * lrDeterminantHd point :=
    mul_pos (mul_pos (by norm_num) hinterior.1.1)
      (lrDeterminantHd_pos hinterior)
  right
  exact (mul_nonneg_iff_of_pos_left hscale).mp hD9

/-- A nonnegative `FirstBracket/e` replay target yields the admitted
first-bracket target because the interior chart has `e > 0`. -/
theorem lrDeterminantAdmittedTarget_of_upperKReplayTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hquotient : 0 ≤ lrFiniteDeterminantUpperKReplayTarget point) :
    LRDeterminantAdmittedTarget point := by
  let first := lrDeterminantFirstBracket
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)
  have hePos : 0 < lrCertificateE point := hinterior.2.1.1
  have hproduct : 0 ≤ lrCertificateE point *
      (first / lrCertificateE point) := by
    exact mul_nonneg hePos.le (by
      simpa [lrFiniteDeterminantUpperKReplayTarget, first] using hquotient)
  have hcancel : lrCertificateE point *
      (first / lrCertificateE point) = first := by
    field_simp [hePos.ne']
  rw [hcancel] at hproduct
  left
  simpa [LRDeterminantFirstBracketAt, first] using hproduct

/-! ## Correct raw-tree replay contract -/

/-- The concrete obligation connecting a raw replay's discard representation
to the verified physical positive-`J` domain.  A generator-specific discard
datatype or checker is not trusted merely because it resembles an existing
Lean datatype: this semantic implication must be proved. -/
def LRFiniteDeterminantRawDiscardCompatible
    {DiscardData : Type}
    (discardCheck : CertificateBox → DiscardData → Bool) : Prop :=
  ∀ box data, discardCheck box data = true →
    ∀ point, box.Contains point → ¬ LRHighShapeVRelevant point

/-- A raw-coordinate tree for the exact D9 target.  Both accepted-leaf
soundness and discard compatibility are explicit kernel-checked fields. -/
structure LRFiniteDeterminantRawD9CheckedTree
    (root : CertificateBox) where
  AcceptData : Type
  DiscardData : Type
  payloadCheck : CertificateBox → AcceptData → Bool
  enclose : CertificateBox → AcceptData → RationalEnclosure
  discardCheck : CertificateBox → DiscardData → Bool
  encloseSound : CheckedEnclosureLeafEvaluatorSound
    lrFiniteDeterminantD9ReplayTarget payloadCheck enclose
  discardCompatible :
    LRFiniteDeterminantRawDiscardCompatible discardCheck
  certificate : SubdivisionCertificate AcceptData DiscardData
  checked : certificate.check
    (checkedEnclosureLeafAccepts payloadCheck enclose)
    discardCheck root = true

namespace LRFiniteDeterminantRawD9CheckedTree

theorem target_nonnegative
    {root : CertificateBox}
    (tree : LRFiniteDeterminantRawD9CheckedTree root)
    {point : CertificatePoint}
    (hpoint : root.Contains point)
    (hrelevant : LRHighShapeVRelevant point) :
    0 ≤ lrFiniteDeterminantD9ReplayTarget point := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    tree.encloseSound tree.discardCompatible tree.checked
    point hpoint hrelevant

end LRFiniteDeterminantRawD9CheckedTree

/-! ## Reusable region adapters -/

/-- Any checked raw D9 tree whose root contains a finite region supplies the
corresponding determinant-ledger theorem. -/
theorem lrFiniteDeterminantD9Region_certificate_of_checkedTree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point → root.Contains point)
    (tree : LRFiniteDeterminantRawD9CheckedTree root) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  exact lrDeterminantAdmittedTarget_of_D9ReplayTarget hinterior
    (tree.target_nonnegative (root_contains hinterior hregion) hrelevant)

/-- Exact `(s,K,h)`-chart counterpart for the corridor's D9 replay.  The
chart tree retains its abstract decoded-discard obligation unchanged. -/
theorem lrFiniteDeterminantD9Region_certificate_of_checkedKChartTree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : LRFiniteDeterminantKChartCheckedTree root
      lrFiniteDeterminantD9ReplayTarget) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hrelevantChart : LRHighShapeVRelevant
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hrelevant
  have hD9 := tree.target_nonnegative
    (root_contains hinterior hregion) hrelevantChart
  rw [hdecoded] at hD9
  exact lrDeterminantAdmittedTarget_of_D9ReplayTarget hinterior hD9

/-- Exact `(s,K,h)`-chart adapter for the audited `FirstBracket/e` target. -/
theorem lrFiniteDeterminantUpperKRegion_certificate_of_checkedKChartTree
    {root : CertificateBox} {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : LRFiniteDeterminantKChartCheckedTree root
      lrFiniteDeterminantUpperKReplayTarget) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hrelevantChart : LRHighShapeVRelevant
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hrelevant
  have hquotient := tree.target_nonnegative
    (root_contains hinterior hregion) hrelevantChart
  rw [hdecoded] at hquotient
  exact lrDeterminantAdmittedTarget_of_upperKReplayTarget
    hinterior hquotient

/-! ## Corrected seven-field replay assembly -/

theorem lrDeterminantFixed1To32Region_certificate_of_D9Tree
    (tree : LRFiniteDeterminantRawD9CheckedTree
      lrDeterminantFixed1To32Root) :
    LRDeterminantRegionCertificateTheorem
      LRDeterminantFixed1To32Region :=
  lrFiniteDeterminantD9Region_certificate_of_checkedTree
    lrDeterminantFixed1To32Root_contains tree

theorem lrDeterminantKCorridorRegion_certificate_of_D9Tree
    (tree : LRFiniteDeterminantKChartCheckedTree
      lrDeterminantKCorridorKChartRoot
      lrFiniteDeterminantD9ReplayTarget) :
    LRDeterminantRegionCertificateTheorem LRDeterminantKCorridorRegion :=
  lrFiniteDeterminantD9Region_certificate_of_checkedKChartTree
    lrDeterminantKCorridorKChartRoot_contains_encode tree

theorem lrDeterminantFixed1To128Region_certificate_of_D9Tree
    (tree : LRFiniteDeterminantRawD9CheckedTree
      lrDeterminantFixed1To128Root) :
    LRDeterminantRegionCertificateTheorem
      LRDeterminantFixed1To128Region :=
  lrFiniteDeterminantD9Region_certificate_of_checkedTree
    lrDeterminantFixed1To128Root_contains tree

theorem lrDeterminantUpperKRegion_certificate_of_quotientTree
    (tree : LRFiniteDeterminantKChartCheckedTree
      lrDeterminantUpperKKChartRoot
      lrFiniteDeterminantUpperKReplayTarget) :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion :=
  lrFiniteDeterminantUpperKRegion_certificate_of_checkedKChartTree
    lrDeterminantUpperKKChartRoot_contains_encode tree

theorem lrDeterminantFixed64Region_certificate_of_D9Tree
    (tree : LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed64Root) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed64Region :=
  lrFiniteDeterminantD9Region_certificate_of_checkedTree
    lrDeterminantFixed64Root_contains tree

theorem lrDeterminantFixed32Region_certificate_of_D9Tree
    (tree : LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed32Root) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed32Region :=
  lrFiniteDeterminantD9Region_certificate_of_checkedTree
    lrDeterminantFixed32Root_contains tree

theorem lrDeterminantFixed16Region_certificate_of_D9Tree
    (tree : LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed16Root) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed16Region :=
  lrFiniteDeterminantD9Region_certificate_of_checkedTree
    lrDeterminantFixed16Root_contains tree

/-- Correct replay-facing tree types for all seven finite ledger fields. -/
structure LRDeterminantFiniteReplayCheckedTrees where
  fixed1To32 :
    LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed1To32Root
  kCorridor : LRFiniteDeterminantKChartCheckedTree
    lrDeterminantKCorridorKChartRoot lrFiniteDeterminantD9ReplayTarget
  fixed1To128 :
    LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed1To128Root
  upperK : LRFiniteDeterminantKChartCheckedTree
    lrDeterminantUpperKKChartRoot lrFiniteDeterminantUpperKReplayTarget
  fixed64 : LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed64Root
  fixed32 : LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed32Root
  fixed16 : LRFiniteDeterminantRawD9CheckedTree lrDeterminantFixed16Root

theorem LRDeterminantFiniteReplayCheckedTrees.toRegionLedger
    (trees : LRDeterminantFiniteReplayCheckedTrees) :
    LRDeterminantFiniteRegionLedger where
  fixed1To32 :=
    lrDeterminantFixed1To32Region_certificate_of_D9Tree trees.fixed1To32
  kCorridor :=
    lrDeterminantKCorridorRegion_certificate_of_D9Tree trees.kCorridor
  fixed1To128 :=
    lrDeterminantFixed1To128Region_certificate_of_D9Tree trees.fixed1To128
  upperK :=
    lrDeterminantUpperKRegion_certificate_of_quotientTree trees.upperK
  fixed64 :=
    lrDeterminantFixed64Region_certificate_of_D9Tree trees.fixed64
  fixed32 :=
    lrDeterminantFixed32Region_certificate_of_D9Tree trees.fixed32
  fixed16 :=
    lrDeterminantFixed16Region_certificate_of_D9Tree trees.fixed16

/-- Assembly of the complete determinant ledger from the four non-finite
inputs and the seven correctly typed replay trees. -/
theorem lrDeterminantRegionLedger_of_finiteReplayCheckedTrees
    (lowRatio : LRDeterminantLowRatioTangentTheorem)
    (deep : LRDeterminantRegionCertificateTheorem LRDeterminantDeepRegion)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (tail : LRDeterminantRegionCertificateTheorem LRDeterminantTailRegion)
    (trees : LRDeterminantFiniteReplayCheckedTrees) :
    LRDeterminantRegionLedger := by
  let finite := trees.toRegionLedger
  exact
    { lowRatio := lowRatio
      deep := deep
      lowK := lowK
      tail := tail
      fixed1To32 := finite.fixed1To32
      kCorridor := finite.kCorridor
      fixed1To128 := finite.fixed1To128
      upperK := finite.upperK
      fixed64 := finite.fixed64
      fixed32 := finite.fixed32
      fixed16 := finite.fixed16 }

end CourtadeKumar
