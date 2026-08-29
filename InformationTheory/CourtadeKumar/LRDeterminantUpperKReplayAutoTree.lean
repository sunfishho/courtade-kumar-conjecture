import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator

/-!
# Auto-sharp checked trees for the upper-`K` determinant replay

This module supplies the structural layer between the deterministic sharp
centered leaf checker and concrete subdivision data.  A packaged tree contains
its complete topology and a kernel proof that the Boolean traversal succeeds;
no topology produced by an external generator is trusted by the theorem.

The two historical upper-`K` trees are the exact children `K ∈ [1,2]` and
`K ∈ [2,4]` of the audited `(s,K,h)` root.  Their discard representations
may differ: the final region adapter combines their soundness geometrically,
without requiring the two certificate datatypes to be identified.
-/

namespace CourtadeKumar

namespace LRUpperKReplayCertificate

/-! ## Soundness of an automatically proposed sharp leaf -/

/-- An accepted deterministic sharp centered leaf proves the replay target
nonnegative at every decoded interior point of its box.  The open-chart part
of the checked payload fixes the sign of `h`; the decoded interior conditions
then turn `0 < h² < 1` into `0 < h < 1`, exactly as in the baseline centered
tree proof. -/
private theorem nonnegative_of_autoSharpCenteredAccepts
    (terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox} {unit : Unit}
    (haccept :
      autoSharpCenteredAccepts terms sqrtFuel logFuel box unit = true)
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
        payloadCheck (centerSKBox box)
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

/-! ## Kernel-checked tree package -/

/-- A complete subdivision tree checked with deterministic sharp centered
payloads.  Accepted leaves store only `Unit`: every analytic payload is
reconstructed from the exact current box by `autoSharpCenteredAccepts`.
Discard soundness remains explicit because no generator-specific discard
representation is trusted merely from its shape. -/
structure AutoSharpCenteredCheckedTree
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  DiscardData : Type
  discardCheck : CertificateBox → DiscardData → Bool
  discardSound : ∀ box data, discardCheck box data = true →
    ∀ coordinate, box.Contains coordinate →
      ¬ LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate)
  certificate : SubdivisionCertificate Unit DiscardData
  checked : certificate.check
    (autoSharpCenteredAccepts terms sqrtFuel logFuel)
    discardCheck root = true

namespace AutoSharpCenteredCheckedTree

/-- Structural subdivision soundness for a deterministic sharp centered
tree.  As in the baseline wrapper, the leaf property is conditional on the
decoded open chart, whereas a discard need only exclude physical relevance. -/
theorem target_nonnegative
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : AutoSharpCenteredCheckedTree
      terms sqrtFuel logFuel root)
    {coordinate : CertificatePoint} (hcoordinate : root.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hconditional := subdivisionCertificate_sound
      (Relevant := fun coordinate ↦
        LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate))
      (Property := fun coordinate ↦
        LRHighShapeInterior (lrDeterminantKChartDecode coordinate) →
          0 ≤ lrFiniteDeterminantUpperKReplayTarget
            (lrDeterminantKChartDecode coordinate))
      (acceptBox := autoSharpCenteredAccepts terms sqrtFuel logFuel)
      (discardBox := tree.discardCheck)
      (box := root) (certificate := tree.certificate)
      (by
        intro box unit haccept point hpoint
        exact nonnegative_of_autoSharpCenteredAccepts
          terms sqrtFuel logFuel haccept hpoint)
      (by
        intro box data hdiscard point hpoint hpointRelevant
        exact (tree.discardSound box data hdiscard point hpoint)
          hpointRelevant)
      tree.checked coordinate hcoordinate hrelevant.2
  exact hconditional hrelevant.1

end AutoSharpCenteredCheckedTree

/-! ## Region adapters -/

/-- Any deterministic sharp centered tree whose root contains an encoded
region supplies that determinant-ledger row. -/
theorem regionCertificate_of_autoSharpCenteredCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : AutoSharpCenteredCheckedTree
      terms sqrtFuel logFuel root) :
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
  exact lrDeterminantAdmittedTarget_of_upperKReplayTarget
    hinterior htarget

/-- Exact `K ∈ [1,2]` child of the audited upper-`K` chart root. -/
abbrev lrDeterminantUpperKOneToTwoKChartRoot : CertificateBox :=
  lrDeterminantUpperKKChartRoot.lower .k 2

/-- Exact `K ∈ [2,4]` child of the audited upper-`K` chart root. -/
abbrev lrDeterminantUpperKTwoToFourKChartRoot : CertificateBox :=
  lrDeterminantUpperKKChartRoot.upper .k 2

/-- The two independently checked historical upper-`K` trees jointly cover
the full audited row.  `contains_lower_or_upper` handles the shared `K = 2`
face, so the trees need neither common certificate topology nor a common
discard datatype. -/
theorem upperKRegionCertificate_of_twoAutoSharpCenteredCheckedTrees
    {terms12 sqrtFuel12 logFuel12 : ℕ}
    {terms24 sqrtFuel24 logFuel24 : ℕ}
    (tree12 : AutoSharpCenteredCheckedTree
      terms12 sqrtFuel12 logFuel12
      lrDeterminantUpperKOneToTwoKChartRoot)
    (tree24 : AutoSharpCenteredCheckedTree
      terms24 sqrtFuel24 logFuel24
      lrDeterminantUpperKTwoToFourKChartRoot) :
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
  rcases CertificateBox.contains_lower_or_upper hroot .k 2 with
      h12 | h24
  · have htarget := tree12.target_nonnegative h12 hchartRelevant
    rw [hdecoded] at htarget
    exact lrDeterminantAdmittedTarget_of_upperKReplayTarget
      hinterior htarget
  · have htarget := tree24.target_nonnegative h24 hchartRelevant
    rw [hdecoded] at htarget
    exact lrDeterminantAdmittedTarget_of_upperKReplayTarget
      hinterior htarget

end LRUpperKReplayCertificate

end CourtadeKumar
