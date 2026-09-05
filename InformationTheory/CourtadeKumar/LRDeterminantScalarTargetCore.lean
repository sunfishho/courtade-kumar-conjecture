import InformationTheory.CourtadeKumar.IntervalSubdivisionCertificate
import InformationTheory.CourtadeKumar.LRCertificateQFunctionCore

/-!
# Lightweight production definitions for the scalar determinant target

These are the unchanged declarations relocated from the analytic assembly
modules. Keeping their original names and bodies makes numerical integration
independent of the large analytic proof import closure. The original modules
now import this one instead of redeclaring these definitions.
-/

namespace CourtadeKumar

def lrCertificateE (point : CertificatePoint) : ℝ :=
  point.s * point.k

def lrCertificateX (point : CertificatePoint) : ℝ :=
  1 - point.chi * lrCertificateE point

noncomputable def lrCertificateV (point : CertificatePoint) : ℝ :=
  Real.sqrt ((1 - lrCertificateE point) / lrCertificateX point)

def lrCertificateB (s y : ℝ) : ℝ :=
  s + (1 - s) * y

noncomputable def lrCertificateOmega (s y : ℝ) : ℝ :=
  lrCertificateQ (lrCertificateB s y) - lrCertificateQ y -
    s * (1 - y) * lrCertificateQPrime (lrCertificateB s y)

def lrCertificateY0 (point : CertificatePoint) : ℝ :=
  point.chi * lrCertificateE point

noncomputable def lrCertificateW (point : CertificatePoint) : ℝ :=
  lrCertificateOmega point.s 0

noncomputable def lrCertificatePWValue (s y0 e v : ℝ) : ℝ :=
  lrCertificateOmega s y0 + lrCertificateOmega s e / v

noncomputable def lrCertificatePW (point : CertificatePoint) : ℝ :=
  lrCertificatePWValue point.s (lrCertificateY0 point)
    (lrCertificateE point) (lrCertificateV point)

noncomputable def lrCertificateG0 (v : ℝ) : ℝ :=
  (1 + 1 / v) * (Real.log (1 + v) - Real.log 2) - Real.log v

noncomputable def lrCertificateGShapeValue (y0 e v : ℝ) : ℝ :=
  lrCertificateG0 v + lrCertificateQ y0 + lrCertificateQ e / v

noncomputable def lrCertificateGShape (point : CertificatePoint) : ℝ :=
  lrCertificateGShapeValue (lrCertificateY0 point)
    (lrCertificateE point) (lrCertificateV point)

noncomputable def lrCertificateBFlowValue (s e v : ℝ) : ℝ :=
  Real.log (1 + v) - (1 / 2 : ℝ) * Real.log (lrCertificateB s e)

noncomputable def lrCertificateBFlow (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowValue point.s (lrCertificateE point)
    (lrCertificateV point)

noncomputable def lrDeterminantY (point : CertificatePoint) : ℝ :=
  lrCertificateB point.s (lrCertificateE point) / lrCertificateE point

noncomputable def lrDeterminantD1 (point : CertificatePoint) : ℝ :=
  let Y := lrDeterminantY point
  (1 / 2 : ℝ) * Real.log ((1 + Y) / 2) + (Y - 1) / (3 * Y + 1)

noncomputable def lrDeterminantPsi (point : CertificatePoint) : ℝ :=
  lrCertificateGShape point + lrCertificatePW point -
    4 * lrCertificateW point / (1 + lrCertificateV point)

noncomputable def lrDeterminantDelta (point : CertificatePoint) : ℝ :=
  (1 - lrCertificateV point * lrCertificateX point) /
    (1 + lrCertificateV point)

noncomputable def lrDeterminantFirstBracket
    (B D1 G psi delta W : ℝ) : ℝ :=
  B * (psi - G + 4 * delta * W) + D1 * psi

def LRDeterminantFirstBracketAt (point : CertificatePoint) : Prop :=
  0 ≤ lrDeterminantFirstBracket
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)

end CourtadeKumar
