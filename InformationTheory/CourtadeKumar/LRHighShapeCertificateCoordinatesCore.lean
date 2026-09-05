import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore
import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import Mathlib.Data.Real.Sqrt

/-!
# Core cancellation coordinates for high-shape certificates

This module contains only the coordinate definitions needed by interval-AD
soundness.  The flow-identification and positive-chart theorems remain in
`LRHighShapeCertificateCoordinates`.
-/

namespace CourtadeKumar



def lrCertificateR (point : CertificatePoint) : ℝ :=
  1 - point.s

noncomputable def lrCertificateT (point : CertificatePoint) : ℝ :=
  Real.sqrt (lrCertificateX point)


end CourtadeKumar
