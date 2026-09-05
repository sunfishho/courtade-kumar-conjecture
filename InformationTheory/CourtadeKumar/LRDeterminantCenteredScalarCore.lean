import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Lightweight cancellation identities for a centered first-bracket evaluator.
These identities supply no numerical bounds and do not discharge a region.
-/
namespace CourtadeKumar

noncomputable def lrDeterminantCenteredShared (p : CertificatePoint) : ℝ :=
  lrCertificateQ (lrCertificateB p.s (lrCertificateY0 p)) +
    lrCertificateQ (lrCertificateB p.s (lrCertificateE p)) / lrCertificateV p -
    p.s * (1 - lrCertificateY0 p) *
      lrCertificateQPrime (lrCertificateB p.s (lrCertificateY0 p)) -
    p.s * (1 - lrCertificateE p) *
      lrCertificateQPrime (lrCertificateB p.s (lrCertificateE p)) / lrCertificateV p

theorem lrDeterminantPsi_eq_centeredShared (p : CertificatePoint) :
    lrDeterminantPsi p = lrCertificateG0 (lrCertificateV p) +
      lrDeterminantCenteredShared p -
      4 * lrCertificateW p / (1 + lrCertificateV p) := by
  unfold lrDeterminantPsi lrCertificateGShape lrCertificateGShapeValue
    lrCertificatePW lrCertificatePWValue lrCertificateOmega lrDeterminantCenteredShared
  ring

theorem lrDeterminantCbase_eq_centeredShared (p : CertificatePoint)
    (hv : 1 + lrCertificateV p ≠ 0) :
    lrDeterminantPsi p - lrCertificateGShape p +
        4 * lrDeterminantDelta p * lrCertificateW p =
      lrDeterminantCenteredShared p - lrCertificateQ (lrCertificateY0 p) -
        lrCertificateQ (lrCertificateE p) / lrCertificateV p -
        4 * lrCertificateV p * lrCertificateX p / (1 + lrCertificateV p) *
          lrCertificateW p := by
  rw [lrDeterminantPsi_eq_centeredShared]
  unfold lrCertificateGShape lrCertificateGShapeValue lrDeterminantDelta
  field_simp
  ring

#print axioms lrDeterminantPsi_eq_centeredShared
#print axioms lrDeterminantCbase_eq_centeredShared
end CourtadeKumar
