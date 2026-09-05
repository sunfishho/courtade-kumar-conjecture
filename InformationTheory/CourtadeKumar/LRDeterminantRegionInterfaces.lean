import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore
import InformationTheory.CourtadeKumar.LRDeterminantRegionCover
import InformationTheory.CourtadeKumar.LRDeterminantFlowCoordinates

/-!
# Lightweight interfaces for the audited determinant-region ledger

Certificate evaluators and generated trees need the exact target and ledger
types, but not the analytic Wronskian and final tangent-closure proofs.  This
module keeps that shared interface below the heavy assembly boundary.
-/

namespace CourtadeKumar


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

end CourtadeKumar
