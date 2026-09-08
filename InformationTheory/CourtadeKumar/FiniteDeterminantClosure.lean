import InformationTheory.CourtadeKumar.MidpointCertificateClosure
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantComplete

/-! The finite determinant is now supplied by a theorem. Only the compact-V
residual certificate remains as a mathematical input to this CK route. -/
namespace CourtadeKumar
open scoped ENNReal NNReal

theorem courtadeKumar_of_compact_certificate
    (compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes) : Statement :=
  courtadeKumar_of_two_certificates
    { compactV := compactV
      finiteDeterminant := LRAnalyticDeterminant.finite }

theorem mutual_information_le_capacity_of_compact_certificate
    (compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes)
    (n : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1 / 2) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one ha) b).toMeasure ≤
      ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) :=
  courtadeKumar_of_compact_certificate compactV n alpha ha b

end CourtadeKumar
