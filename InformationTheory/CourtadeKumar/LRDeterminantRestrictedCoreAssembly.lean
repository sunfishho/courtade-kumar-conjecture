import InformationTheory.CourtadeKumar.LRGapBudgetSEFourTailFlowAssembly
import InformationTheory.CourtadeKumar.LRDeterminantBoundedDeepRestoration
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioSmallSAnalytic

/-!
# Restricted determinant assembly for the `k <= 4` tangent core

The replayed gap-budget tail already closes the near-endpoint tangent
obligation for `k >= 4`.  Consequently the final LR flow does not require a
global `LRDeterminantRegionLedger`: it is enough to prove the audited
determinant rows after intersecting them with `k <= 4`.

On the deep row we use the already-required low-`k` theorem whenever
`k <= 1`.  The bounded-deep ideal and restoration arguments are therefore
needed only on the compact band `1 <= k <= 4`; neither the first coarse root
near `k = 1/32` nor the high band up to `k = 128` enters this assembly.
-/

open Set

namespace CourtadeKumar

/-! ## Restricted certificate interfaces -/

/-- A determinant-row theorem restricted to the part of the row with
`k <= 4`.  This is the exact strength needed by the gap-budget core/tail
split. -/
def LRDeterminantKLeFourRegionCertificateTheorem
    (Region : CertificatePoint → Prop) : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    Region point →
    point.k ≤ 4 →
    LRDeterminantAdmittedTarget point

/-- Any unrestricted determinant-row theorem supplies its `k <= 4`
restriction. -/
theorem lrDeterminantKLeFourRegionCertificate_of_unrestricted
    {Region : CertificatePoint → Prop}
    (hregion : LRDeterminantRegionCertificateTheorem Region) :
    LRDeterminantKLeFourRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hpoint _hk
  exact hregion point hinterior hrelevant hpoint

/-- The only genuinely deep determinant band left after reusing the low-`k`
row: `s <= 2^-14` and `1 <= k <= 4`. -/
def LRDeterminantDeepOneToFourCertificateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantDeepRegion point →
    1 ≤ point.k →
    point.k ≤ 4 →
    LRDeterminantAdmittedTarget point

/-- Ideal-core margin needed on the restricted deep band. -/
def LRDeterminantIdealOneToFourTheorem : Prop :=
  ∀ {L : ℝ}, lrDeterminantIdealDeepL0 ≤ L →
    ∀ k chi : ℝ,
      k ∈ Icc (1 : ℝ) 4 →
      chi ∈ Icc (0 : ℝ) 1 →
      (3 / 5 : ℝ) < lrDeterminantIdealCore L k chi

/-- Exact ideal-to-actual loss needed on `1 <= k <= 4`.  Only the low-band
DA3 budget appears. -/
def LRDeterminantDeepOneToFourRestorationTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantDeepRegion point →
    1 ≤ point.k →
    point.k ≤ 4 →
    lrDeterminantIdealCore (Real.log (1 / point.s))
          point.k point.chi - lrLowKActualNormalized point ≤
      (lrDeterminantLowBandRestorationBudget : ℝ)

/-- The seven finite determinant rows, each restricted to `k <= 4`.
The analytic `k >= 4` gap-budget tail makes a determinant tail field
unnecessary. -/
structure LRDeterminantKLeFourFiniteRegionLedger : Prop where
  fixed1To32 : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFixed1To32Region
  kCorridor : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantKCorridorRegion
  fixed1To128 : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFixed1To128Region
  upperK : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantUpperKRegion
  fixed64 : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFixed64Region
  fixed32 : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFixed32Region
  fixed16 : LRDeterminantKLeFourRegionCertificateTheorem
    LRDeterminantFixed16Region

/-! ## Restricted bounded-deep adapter -/

/-- On `1 <= k <= 4`, the ideal margin and only the low-band restoration
budget give the admitted cleared determinant target. -/
theorem lrDeterminantDeepOneToFour_certificate_of_ideal_and_restoration
    (ideal : LRDeterminantIdealOneToFourTheorem)
    (restoration : LRDeterminantDeepOneToFourRestorationTheorem) :
    LRDeterminantDeepOneToFourCertificateTheorem := by
  intro point hinterior hrelevant hdeep hkOne hkFour
  have hsIoc : point.s ∈ Ioc (0 : ℝ) (1 / 16384) :=
    ⟨hinterior.1.1, hdeep.1⟩
  have hL : lrDeterminantIdealDeepL0 ≤
      Real.log (1 / point.s) := by
    simpa [lrDeterminantIdealDeepL0] using
      lrSmallSBridge_log_lower hsIoc
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 :=
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  have hideal : (3 / 5 : ℝ) <
      lrDeterminantIdealCore (Real.log (1 / point.s))
        point.k point.chi :=
    ideal hL point.k point.chi ⟨hkOne, hkFour⟩ hchi
  have hloss := restoration point hinterior hrelevant hdeep hkOne hkFour
  have hrestored : (23 / 40 : ℝ) < lrLowKActualNormalized point :=
    lrDeterminantRestored_gt_twenty_three_fortieths hideal hloss
  have hnormalized : 0 < lrLowKActualNormalized point :=
    (by norm_num : (0 : ℝ) < 23 / 40).trans hrestored
  have hn := lrLowKNormalization_pos hinterior
  have hcleared : 0 < lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point) := by
    have hproduct := mul_pos hnormalized hn
    unfold lrLowKActualNormalized at hproduct
    rw [div_mul_cancel₀ _ hn.ne'] at hproduct
    exact hproduct
  exact Or.inr hcleared.le

/-! ## Determinant cover restricted to the tangent core -/

/-- The audited determinant cover, restricted to `k <= 4`.  Deep points
with `k <= 1` are sent to the low-`k` theorem; deep points above one use only
the `1 <= k <= 4` certificate.  The determinant tail case is impossible. -/
theorem lrCertificateTTarget_nonnegative_of_kLeFour_determinantCovered
    (deepOneToFour : LRDeterminantDeepOneToFourCertificateTheorem)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (finite : LRDeterminantKLeFourFiniteRegionLedger)
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hkFour : point.k ≤ 4)
    (hcovered : LRDeterminantCovered point) :
    0 ≤ lrCertificateTTarget point := by
  rcases hcovered with hdeep | hlowK | htail | hfixed1To32 |
      hkCorridor | hfixed1To128 | hupperK | hfixed64 | hfixed32 | hfixed16
  · by_cases hkOne : point.k ≤ 1
    · apply lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
        hinterior hrelevant
      exact lowK point hinterior hrelevant
        ⟨hdeep.1.trans (by norm_num), hdeep.2, hkOne⟩
    · apply lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
        hinterior hrelevant
      exact deepOneToFour point hinterior hrelevant hdeep
        (lt_of_not_ge hkOne).le hkFour
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (lowK point hinterior hrelevant hlowK)
  · have himpossible : (32 : ℝ) ≤ 4 := htail.2.trans hkFour
    norm_num at himpossible
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.fixed1To32 point hinterior hrelevant hfixed1To32 hkFour)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.kCorridor point hinterior hrelevant hkCorridor hkFour)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.fixed1To128 point hinterior hrelevant hfixed1To128 hkFour)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.upperK point hinterior hrelevant hupperK hkFour)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.fixed64 point hinterior hrelevant hfixed64 hkFour)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.fixed32 point hinterior hrelevant hfixed32 hkFour)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (finite.fixed16 point hinterior hrelevant hfixed16 hkFour)

/-- A near-endpoint low-ratio theorem and the restricted determinant inputs
give exactly the tangent-core interface consumed by the verified `k >= 4`
gap-budget tail. -/
theorem nearEndpointCoreTangentCoordinateTheorem_of_restrictedDeterminant
    (lowRatio : LRDeterminantNearEndpointLowRatioTangentTheorem)
    (deepOneToFour : LRDeterminantDeepOneToFourCertificateTheorem)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) :
    LRHighShapeNearEndpointCoreTangentCoordinateTheorem := by
  intro point hinterior hrelevant hsUpper hkFour
  rcases lrHighShape_lowRatio_or_determinantCovered
      hinterior hrelevant hsUpper with hlowRatio | hcovered
  · exact lowRatio point hinterior hrelevant hsUpper hlowRatio
  · exact lrCertificateTTarget_nonnegative_of_kLeFour_determinantCovered
      deepOneToFour lowK finite hinterior hrelevant hkFour hcovered

/-- End-to-end restricted tangent-core assembly from the already proved
small-`s` low-ratio theorem, the finite direct-`V` input, and the restricted
determinant data. -/
theorem nearEndpointCoreTangentCoordinateTheorem_of_restrictedAuditedParts
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (ideal : LRDeterminantIdealOneToFourTheorem)
    (restoration : LRDeterminantDeepOneToFourRestorationTheorem)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) :
    LRHighShapeNearEndpointCoreTangentCoordinateTheorem :=
  nearEndpointCoreTangentCoordinateTheorem_of_restrictedDeterminant
    (lrDeterminantNearEndpointLowRatioTangentTheorem_of_smallSFirstBracket_and_finiteV
      lrDeterminantLowRatioSmallSFirstBracketTheorem finiteV)
    (lrDeterminantDeepOneToFour_certificate_of_ideal_and_restoration
      ideal restoration)
    lowK finite

/-! ## Direct feed into the compact-core flow closure -/

/-- The compact channel ledger, the post-small-`s` midpoint theorem, and the
restricted determinant inputs prove the exact flow numerator.  No full
determinant ledger or determinant theorem above `k = 4` is used. -/
theorem lrFlowNumeratorP_nonneg_target_of_restrictedDeterminantCore
    (compactV : LRCompactVR910ReplayLedger)
    (midpoint :
      LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (ideal : LRDeterminantIdealOneToFourTheorem)
    (restoration : LRDeterminantDeepOneToFourRestorationTheorem)
    (lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion)
    (finite : LRDeterminantKLeFourFiniteRegionLedger)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t :=
  lrFlowNumeratorP_nonneg_target_of_compact_core_certificates
    compactV midpoint
    (nearEndpointCoreTangentCoordinateTheorem_of_restrictedAuditedParts
      finiteV ideal restoration lowK finite)
    hR hp hv ht htarget

end CourtadeKumar
