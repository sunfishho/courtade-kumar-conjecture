import InformationTheory.CourtadeKumar.FiniteDeterminantClosure
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactComplete

/-! All four certificate families are supplied in this assembly.
The compact-V batches use kernel-checked integer interval arithmetic,
alongside the kernel-checked finite-V, midpoint, and finite-determinant certificates. -/
namespace CourtadeKumar
open scoped ENNReal NNReal

theorem courtadeKumar_via_completed_certificates : Statement :=
  courtadeKumar_of_compact_certificate
    (LRCompactReducedCertificate.residual lrCompactVVerifiedBoxes)

theorem mutual_information_le_capacity_via_completed_certificates
    (n : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1/2) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one ha) b).toMeasure ≤
      ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) :=
  courtadeKumar_via_completed_certificates n alpha ha b

end CourtadeKumar
