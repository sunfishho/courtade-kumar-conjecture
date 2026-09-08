import InformationTheory.CourtadeKumar.AnalyticCertificateClosure
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointSmallK
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointCore
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantLoss

/-! The three-family closure with the enlarged analytic midpoint face
removed. The other two families remain unchanged explicit inputs. -/
namespace CourtadeKumar

namespace LRAnalyticMidpoint

/-- Exact remaining midpoint domain after the whole k≤1/4 face is proved. -/
def UpperKCertificate : Prop :=
  ∀ p : CertificatePoint, LRHighShapeInterior p → LRHighShapeVRelevant p →
    1 / 4 < p.k → p.k ≤ 4 → 1 / 16384 < p.s → p.s < 1 / 10 →
    0 ≤ lrCertificateUTarget p

theorem midpoint_of_upper_k (remaining : UpperKCertificate) :
    LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointCompactMidpointCoordinateTheorem := by
  intro p hi hr _hkLo hk _hmid hsLo hs
  by_cases hsmall : p.k ≤ 1 / 4
  · exact midpoint_small_k hi hr hs.le hsmall
  · exact remaining p hi hr (lt_of_not_ge hsmall) hk hsLo hs

theorem upper_k_iff_original : UpperKCertificate ↔
    LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointCompactMidpointCoordinateTheorem := by
  refine ⟨midpoint_of_upper_k, ?_⟩
  intro h p hi hr hkLo hk hsLo hs
  exact h p hi hr (by linarith) hk (Or.inr hkLo) hsLo hs

/-- A sufficient alternative using only the reduced logarithmic target. -/
def UpperKCoreCertificate : Prop :=
  ∀ p : CertificatePoint, LRHighShapeInterior p → LRHighShapeVRelevant p →
    1 / 4 < p.k → p.k ≤ 4 → 1 / 16384 < p.s → p.s < 1 / 10 →
    0 ≤ coreTarget p

theorem upper_k_of_core (remaining : UpperKCoreCertificate) : UpperKCertificate := by
  intro p hi hr hkLo hk hsLo hs
  exact midpoint_of_core hi hr hs.le hk (remaining p hi hr hkLo hk hsLo hs)

end LRAnalyticMidpoint

/-- The midpoint input is smaller; compact V and finite determinant are
still open on their original domains. -/
structure RemainingReducedAnalyticCertificates : Prop where
  compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes
  midpoint : LRAnalyticMidpoint.UpperKCertificate
  finiteDeterminant : LRDeterminantKLeFourFiniteCompressedCertificateTheorem

def RemainingReducedAnalyticCertificates.toAnalytic
    (c : RemainingReducedAnalyticCertificates) : RemainingAnalyticCertificates where
  compactV := c.compactV
  midpoint := LRAnalyticMidpoint.midpoint_of_upper_k c.midpoint
  finiteDeterminant := c.finiteDeterminant

theorem courtadeKumar_of_reduced_analytic_certificates
    (c : RemainingReducedAnalyticCertificates) : Statement :=
  courtadeKumar_of_analytic_certificates c.toAnalytic

namespace LRAnalyticDeterminant

/-- A sufficient replacement on the same finite domain. The first-bracket
branch remains available where the uniform D-model payment is too coarse. -/
def FiniteMarginCertificate : Prop :=
  ∀ p : CertificatePoint, LRHighShapeInterior p → LRHighShapeVRelevant p →
    LRDeterminantKLeFourFiniteCompressedRegion p → p.s < p.k → p.k ≤ 4 →
    LRDeterminantFirstBracketAt p ∨
      (1 / 75 : ℝ) * max 0 (lrDeterminantPsi p - lrDeterminantC0 p * lrDeterminantT p) ≤
        exactCompensated p

theorem finite_of_margin (remaining : FiniteMarginCertificate) :
    LRDeterminantKLeFourFiniteCompressedCertificateTheorem := by
  intro p hi hr hregion hsk hk
  rcases remaining p hi hr hregion hsk hk with hfirst | hmargin
  · exact Or.inl hfirst
  · exact Or.inr (cleared_of_exact_margin hi hmargin)

end LRAnalyticDeterminant

/-- An optional alternative interface for smaller future certificates.
Neither of its reduced targets is assumed to have been proved universally. -/
structure RemainingAnalyticCoreCertificates : Prop where
  compactV : LRCompactVResidualLedger lrCompactVVerifiedBoxes
  midpoint : LRAnalyticMidpoint.UpperKCoreCertificate
  finiteDeterminant : LRAnalyticDeterminant.FiniteMarginCertificate

def RemainingAnalyticCoreCertificates.toReduced
    (c : RemainingAnalyticCoreCertificates) : RemainingReducedAnalyticCertificates where
  compactV := c.compactV
  midpoint := LRAnalyticMidpoint.upper_k_of_core c.midpoint
  finiteDeterminant := LRAnalyticDeterminant.finite_of_margin c.finiteDeterminant

theorem courtadeKumar_of_analytic_core_certificates
    (c : RemainingAnalyticCoreCertificates) : Statement :=
  courtadeKumar_of_reduced_analytic_certificates c.toReduced

end CourtadeKumar
