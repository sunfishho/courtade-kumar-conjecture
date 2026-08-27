import InformationTheory.CourtadeKumar.LRHighShapeVMidpointEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Genuinely centered direct-`V` certificates

The generic midpoint theorem needs only a value enclosure at the rational
center of a box, plus derivative enclosures on the whole box.  Using one
whole-box evaluation for both roles is sound but unnecessarily loses the
same interval dependency twice.  This module separates those two payloads.
-/

namespace CourtadeKumar

def CertificateBox.centerBox (box : CertificateBox) : CertificateBox :=
  let s := RationalEnclosure.center box.sInterval
  let k := RationalEnclosure.center box.kInterval
  let chi := RationalEnclosure.center box.chiInterval
  { sLo := s, sHi := s, kLo := k, kHi := k,
    chiLo := chi, chiHi := chi }

theorem CertificateBox.centerBox_contains_midpoint (box : CertificateBox) :
    box.centerBox.Contains box.midpoint := by
  simp [CertificateBox.centerBox, CertificateBox.midpoint,
    CertificateBox.Contains]

structure LRHighShapeVCenteredCertificate where
  center : LRHighShapeVCertificate
  derivative : LRHighShapeVCertificate

namespace LRHighShapeVCenteredCertificate

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (derivative : LRHighShapeVCertificate :=
      LRHighShapeVCertificate.auto sqrtFuel logFuel box) :
    LRHighShapeVCenteredCertificate :=
  { center := LRHighShapeVCertificate.auto sqrtFuel logFuel box.centerBox
    derivative := derivative }

def payloadCheck (box : CertificateBox)
    (certificate : LRHighShapeVCenteredCertificate) : Bool :=
  lrHighShapeInteriorBoxCheck box &&
    certificate.center.check box.centerBox &&
    certificate.derivative.check box

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCenteredCertificate) : MidpointCertificate :=
  let centerResult := certificate.center.evaluateAD terms box.centerBox
  let derivativeResult := certificate.derivative.evaluateAD terms box
  { value := centerResult.value
    derivS := derivativeResult.derivS
    derivK := derivativeResult.derivK
    derivChi := derivativeResult.derivChi }

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCenteredCertificate) : Bool :=
  checkedMidpointLeafAccepts payloadCheck (evaluate terms) box certificate

noncomputable def derivativeEnclosures (terms : ℕ)
    {box : CertificateBox} {certificate : LRHighShapeVCenteredCertificate}
    (hcheck : certificate.derivative.check box = true)
    (hinterior : ∀ point, box.Contains point → LRHighShapeInterior point) :
    BoxDerivativeEnclosures lrCertificateVTarget box
      (certificate.evaluate terms box) := by
  refine
    { partialS := lrCertificateVTargetDerivS
      partialK := lrCertificateVTargetDerivK
      partialChi := lrCertificateVTargetDerivChi
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point hpoint
    exact hasDerivAt_lrCertificateVTarget_s (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateVTarget_k (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateVTarget_chi (hinterior point hpoint)
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.2.2

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedMidpointLeafEvaluatorSound lrCertificateVTarget payloadCheck
      (evaluate terms) := by
  constructor
  · intro box certificate hpayload
    have hparts :
        (lrHighShapeInteriorBoxCheck box = true ∧
          certificate.center.check box.centerBox = true) ∧
        certificate.derivative.check box = true := by
      simpa [payloadCheck] using hpayload
    have hcenter := certificate.center.evaluateAD_sound terms
      box.centerBox_contains_midpoint hparts.1.2
    simpa [evaluate] using hcenter.1
  · intro box certificate hpayload
    have hparts :
        (lrHighShapeInteriorBoxCheck box = true ∧
          certificate.center.check box.centerBox = true) ∧
        certificate.derivative.check box = true := by
      simpa [payloadCheck] using hpayload
    exact certificate.derivativeEnclosures terms hparts.2
      (fun _point hpoint ↦
        lrHighShapeInteriorBoxCheck_sound hparts.1.1 hpoint)

end LRHighShapeVCenteredCertificate

theorem lrHighShapeVCenteredSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeVCenteredCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeVCenteredCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateVTarget point := by
  exact subdivisionCertificate_nonnegative_checked
    (LRHighShapeVCenteredCertificate.checkedEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

end CourtadeKumar
