import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator
import InformationTheory.CourtadeKumar.LRCertificateQSecondPointEnclosure
import InformationTheory.CourtadeKumar.LRCertificateQRegularizedScale

/-!
# Three-coordinate base for the historical upper-K replay

This module isolates the exact midpoint geometry and the genuine derivative in
the squared-channel chart coordinate.  Replay points satisfy `0 < h < 1`,
while their enclosing boxes may nevertheless touch `h = 0`.
-/

open Set

namespace CourtadeKumar.LRUpperKHistoricalThreeCoordinateBase

open LRUpperKReplayCertificate

/-- The exact rational singleton at the ordinary `(s,K,h)` midpoint. -/
def centerBox (box : CertificateBox) : CertificateBox :=
  let s := RationalEnclosure.center box.sInterval
  let K := RationalEnclosure.center box.kInterval
  let h := RationalEnclosure.center box.chiInterval
  { sLo := s, sHi := s, kLo := K, kHi := K,
    chiLo := h, chiHi := h }

theorem centerBox_contains_midpoint (box : CertificateBox) :
    (centerBox box).Contains box.midpoint := by
  simp [centerBox, CertificateBox.midpoint, CertificateBox.Contains]

/-- Exact derivative of the decoded target in the chart variable `h`, where
the raw channel coordinate is `chi = h^2`. -/
noncomputable def targetChartDerivH
    (coordinate : CertificatePoint) : ℝ :=
  targetRawDeriv (lrDeterminantKChartDecode coordinate)
    0 0 (2 * coordinate.chi)

theorem hasDerivAt_targetChart_h {coordinate : CertificatePoint}
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate)) :
    HasDerivAt
      (fun h ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode { coordinate with chi := h }))
      (targetChartDerivH coordinate) coordinate.chi := by
  have h := hasDerivAt_targetRaw_curve
    (sfun := fun _ ↦ coordinate.s)
    (kfun := fun _ ↦ coordinate.s * coordinate.k)
    (chifun := fun h ↦ h ^ 2)
    (hasDerivAt_const coordinate.chi coordinate.s)
    (hasDerivAt_const coordinate.chi
      (coordinate.s * coordinate.k))
    (by simpa [pow_two] using
      ((hasDerivAt_id coordinate.chi).mul
        (hasDerivAt_id coordinate.chi)))
    hinterior
  simpa [targetChartDerivH, lrCertificateCurve,
    lrDeterminantKChartDecode, pow_two, two_mul] using h

end CourtadeKumar.LRUpperKHistoricalThreeCoordinateBase
