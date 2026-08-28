import InformationTheory.CourtadeKumar.LRDeterminantRegionCover
import InformationTheory.CourtadeKumar.LRDeterminantWronskianConcrete
import InformationTheory.CourtadeKumar.LRNearEndpointTangentAssembly

/-!
# Assembly of the audited determinant-region ledger

The audited near-endpoint proof has one direct low-ratio branch and ten
determinant regions.  A determinant-region row may establish either the
cheaper first bracket (D5) or the fully cleared singular determinant (D4).
This file records those alternatives faithfully and proves that a ledger
covering every row supplies the complete near-endpoint tangent theorem.

The analytic coefficient sign needed to pass from (D4) to the tangent target
is no longer a ledger assumption: it follows from the exact Wronskian
resummation in `LRDeterminantWronskianConcrete`.
-/

namespace CourtadeKumar

/-- The cheaper (D5) scalar inequality at a certificate point. -/
def LRDeterminantFirstBracketAt (point : CertificatePoint) : Prop :=
  0 ≤ lrDeterminantFirstBracket
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)

/-- The fully cleared singular determinant (D4) at a certificate point. -/
def LRDeterminantClearedSingularAt (point : CertificatePoint) : Prop :=
  0 ≤ lrDeterminantClearedSingular
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)
    (lrDeterminantC0 point) (lrCertificateX point)
    (lrDeterminantT point)

/-- The two scalar certificate formats accepted in the audited region table. -/
def LRDeterminantAdmittedTarget (point : CertificatePoint) : Prop :=
  LRDeterminantFirstBracketAt point ∨
    LRDeterminantClearedSingularAt point

/-- Either audited determinant certificate format implies the coordinate
tangent target.  In the cleared-determinant branch, the coefficient sign is
supplied by the analytic Wronskian theorem rather than by the region ledger. -/
theorem lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hadmitted : LRDeterminantAdmittedTarget point) :
    0 ≤ lrCertificateTTarget point := by
  rcases hadmitted with hfirst | hcleared
  · exact lrCertificateTTarget_nonnegative_of_firstBracket_analytic
      hinterior hrelevant hfirst
  · exact lrCertificateTTarget_nonnegative_of_clearedSingular_core
      hinterior hrelevant
      (lrCertificateDeterminantCoefficient_nonnegative hinterior)
      hcleared

/-- A region theorem has precisely the hypotheses common to every row of the
audited determinant table. -/
def LRDeterminantRegionCertificateTheorem
    (Region : CertificatePoint → Prop) : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    Region point →
    LRDeterminantAdmittedTarget point

/-- The direct theorem used on the exceptional low-ratio strip
`1/4 < k/s ≤ 1`. -/
def LRDeterminantLowRatioTangentTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantLowRatioRegion point →
    0 ≤ lrCertificateTTarget point

/-- The eleven proof obligations in the audited near-endpoint determinant
decomposition: one direct low-ratio strip and ten determinant rows. -/
structure LRDeterminantRegionLedger where
  lowRatio : LRDeterminantLowRatioTangentTheorem
  deep : LRDeterminantRegionCertificateTheorem LRDeterminantDeepRegion
  lowK : LRDeterminantRegionCertificateTheorem LRDeterminantLowKRegion
  tail : LRDeterminantRegionCertificateTheorem LRDeterminantTailRegion
  fixed1To32 :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed1To32Region
  kCorridor :
    LRDeterminantRegionCertificateTheorem LRDeterminantKCorridorRegion
  fixed1To128 :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed1To128Region
  upperK : LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion
  fixed64 : LRDeterminantRegionCertificateTheorem LRDeterminantFixed64Region
  fixed32 : LRDeterminantRegionCertificateTheorem LRDeterminantFixed32Region
  fixed16 : LRDeterminantRegionCertificateTheorem LRDeterminantFixed16Region

/-- Every row in a determinant ledger supplies the tangent target on the
union of the ten audited determinant regions. -/
theorem lrCertificateTTarget_nonnegative_of_determinantCovered
    (ledger : LRDeterminantRegionLedger)
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hcovered : LRDeterminantCovered point) :
    0 ≤ lrCertificateTTarget point := by
  rcases hcovered with hdeep | hlowK | htail | hfixed1To32 |
      hkCorridor | hfixed1To128 | hupperK | hfixed64 | hfixed32 | hfixed16
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.deep point hinterior hrelevant hdeep)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.lowK point hinterior hrelevant hlowK)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.tail point hinterior hrelevant htail)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (ledger.fixed1To32 point hinterior hrelevant hfixed1To32)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (ledger.kCorridor point hinterior hrelevant hkCorridor)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant
      (ledger.fixed1To128 point hinterior hrelevant hfixed1To128)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.upperK point hinterior hrelevant hupperK)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.fixed64 point hinterior hrelevant hfixed64)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.fixed32 point hinterior hrelevant hfixed32)
  · exact lrCertificateTTarget_nonnegative_of_determinantAdmittedTarget
      hinterior hrelevant (ledger.fixed16 point hinterior hrelevant hfixed16)

/-- The exact region split (D12)--(D13) turns a complete determinant ledger
into the near-endpoint coordinate theorem. -/
theorem nearEndpointTangentCoordinateTheorem_of_determinantRegionLedger
    (ledger : LRDeterminantRegionLedger) :
    LRHighShapeNearEndpointTangentCoordinateTheorem := by
  intro point hinterior hrelevant hsUpper
  rcases lrHighShape_lowRatio_or_determinantCovered
      hinterior hrelevant hsUpper with hlowRatio | hcovered
  · exact ledger.lowRatio point hinterior hrelevant hlowRatio
  · exact lrCertificateTTarget_nonnegative_of_determinantCovered
      ledger hinterior hrelevant hcovered

/-- Flow-level endpoint theorem furnished by a complete audited determinant
ledger. -/
theorem nearEndpointTangentTheorem_of_determinantRegionLedger
    (ledger : LRDeterminantRegionLedger) :
    LRHighShapeNearEndpointTangentTheorem :=
  nearEndpointTangentTheorem_of_coordinateTheorem
    (nearEndpointTangentCoordinateTheorem_of_determinantRegionLedger ledger)

end CourtadeKumar
