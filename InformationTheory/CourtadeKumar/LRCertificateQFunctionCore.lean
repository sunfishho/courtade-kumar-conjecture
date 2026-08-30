import InformationTheory.CourtadeKumar.TopEntropyScalarCore
import InformationTheory.CourtadeKumar.TopPsiDerivativeCore

/-!
# Lightweight function core for LR `Q/Q'` certificates

Only the two functions interpreted by point certificates live here.  The
second derivative and the global analytic properties remain in
`LRCertificateQ`.
-/

namespace CourtadeKumar

/-- The scalar `Q` used in the midpoint and determinant certificate ledgers. -/
noncomputable def lrCertificateQ (y : ℝ) : ℝ :=
  topJ (Real.sqrt (1 - y))

/-- The manuscript expression for `Q'`. -/
noncomputable def lrCertificateQPrime (y : ℝ) : ℝ :=
  topPsiDeriv (1 - y)

lemma lrCertificateQPrime_eq (y : ℝ) :
    lrCertificateQPrime y =
      Real.artanh (Real.sqrt (1 - y)) /
        (2 * Real.sqrt (1 - y)) := by
  rfl

end CourtadeKumar
