import InformationTheory.CourtadeKumar.CertificateClosure
import InformationTheory.CourtadeKumar.AnalyticExtension.DirectV

/-! Courtade-Kumar with three remaining certificate families. The low-ratio
finite-V premise is now supplied by an analytic proof on its entire domain. -/
namespace CourtadeKumar
open scoped ENNReal NNReal

/-- The numerical finite-V family has been eliminated. These three remaining
families are still open mathematical inputs. -/
structure RemainingAnalyticCertificates : Prop where
  compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes
  midpoint :
    LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointCompactMidpointCoordinateTheorem
  finiteDeterminant : LRDeterminantKLeFourFiniteCompressedCertificateTheorem

def RemainingAnalyticCertificates.toRemainingCertificates
    (c : RemainingAnalyticCertificates) : RemainingCertificates where
  compactV := c.compactV
  midpoint := c.midpoint
  finiteV := LRLowRatioDirectV.finiteV
  finiteDeterminant := c.finiteDeterminant

theorem courtadeKumar_of_analytic_certificates (c : RemainingAnalyticCertificates) : Statement :=
  courtadeKumar_of_certificates c.toRemainingCertificates

theorem mutual_information_le_capacity_of_analytic_certificates
    (c : RemainingAnalyticCertificates)
    (n : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1 / 2) (b : BitVec n → Bool) :
    InformationQuantities.mutual_information
        (bscJointPMF n alpha (crossover_le_one ha) b).toMeasure ≤
      ENNReal.ofReal (1 - binaryEntropyBits (alpha : ℝ)) :=
  courtadeKumar_of_analytic_certificates c n alpha ha b

end CourtadeKumar
