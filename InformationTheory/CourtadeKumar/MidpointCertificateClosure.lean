import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointComplete

/-! Courtade-Kumar with two remaining certificate families. The complete
finite-V and midpoint inputs are now supplied by checked Lean theorems. -/
namespace CourtadeKumar
open scoped ENNReal NNReal

/-- Only compact V and finite determinant remain free mathematical inputs. -/
structure RemainingTwoCertificates : Prop where
  compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes
  finiteDeterminant : LRDeterminantKLeFourFiniteCompressedCertificateTheorem

def RemainingTwoCertificates.toReduced
    (c : RemainingTwoCertificates) : RemainingReducedAnalyticCertificates where
  compactV := c.compactV
  midpoint := LRAnalyticMidpoint.upper_k
  finiteDeterminant := c.finiteDeterminant

theorem courtadeKumar_of_two_certificates (c : RemainingTwoCertificates) : Statement :=
  courtadeKumar_of_reduced_analytic_certificates c.toReduced

theorem mutual_information_le_capacity_of_two_certificates
    (c : RemainingTwoCertificates)
    (n : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1 / 2) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one ha) b).toMeasure ≤
      ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) :=
  courtadeKumar_of_two_certificates c n alpha ha b

end CourtadeKumar
