import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Data.Real.Sqrt

/-!
# Lightweight TOP radial derivative scalar

The exact point-certificate function `lrCertificateQPrime` is definitionally
expressed through `topPsiDeriv`.  Its formula is isolated here so point proofs
do not import the normalized-reserve and cap developments.
-/

namespace CourtadeKumar

noncomputable def topPsiDeriv (R : ℝ) : ℝ :=
  Real.artanh (Real.sqrt R) / (2 * Real.sqrt R)

end CourtadeKumar
