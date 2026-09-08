import InformationTheory.CourtadeKumar.LRDeterminantRestrictedAnalyticClosure
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteRegionCompression
import InformationTheory.CourtadeKumar.LRCompactVVerifiedCover

/-!
# Courtade–Kumar from the four remaining certificate families

The compact-V input concerns only the complement of the two verified boxes.
The midpoint input uses the proved positive lower bound on `k`, and the
finite determinant input uses the exact compressed union of the historical
rows. All analytic restoration and global trajectory inputs are supplied by
the imported closure theorems.

`RemainingCertificates` records open proof obligations. This module does not
construct an inhabitant of that structure or assert an unconditional proof
of `Statement`.
-/

namespace CourtadeKumar

open scoped ENNReal NNReal

/-- The four remaining mathematical inputs, after applying the existing
coverage and coordinate reductions. -/
structure RemainingCertificates : Prop where
  compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes
  midpoint :
    LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointCompactMidpointCoordinateTheorem
  finiteV : LRDeterminantLowRatioFiniteVTargetTheorem
  finiteDeterminant : LRDeterminantKLeFourFiniteCompressedCertificateTheorem

/-- The original restricted closure, with the already-verified compact-V
boxes removed from its first premise. -/
theorem courtadeKumar_of_remainingRestrictedCertificates_outsideVerifiedCompactV
    (compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes)
    (midpoint :
      LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (finiteV : LRDeterminantLowRatioFiniteVTargetTheorem)
    (finite : LRDeterminantKLeFourFiniteRegionLedger) : Statement :=
  courtadeKumar_of_remainingRestrictedCertificates
    (lrCompactVSoundLedger_of_verifiedResidual compactV) midpoint finiteV finite

/-- Filling the four explicitly recorded certificate families proves the
full mutual-information statement for every dimension and BSC parameter. -/
theorem courtadeKumar_of_certificates (certificates : RemainingCertificates) :
    Statement :=
  courtadeKumar_of_remainingRestrictedCertificates_outsideVerifiedCompactV
    certificates.compactV
    (LRSmallSBridgeCoreCertificate.postSmallSBridgeMidpointCoordinate_of_compact
      certificates.midpoint)
    certificates.finiteV
    (lrDeterminantKLeFourFiniteRegionLedger_of_compressed
      certificates.finiteDeterminant)

/-- The expanded mutual-information conclusion of the conditional closure. -/
theorem mutual_information_le_capacity_of_certificates
    (certificates : RemainingCertificates)
    (n : ℕ) (alpha : ℝ≥0) (halpha : alpha ≤ 1 / 2)
    (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one halpha) b).toMeasure
      ≤ ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) :=
  courtadeKumar_of_certificates certificates n alpha halpha b

end CourtadeKumar
