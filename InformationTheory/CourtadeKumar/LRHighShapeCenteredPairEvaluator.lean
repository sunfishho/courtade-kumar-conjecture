import InformationTheory.CourtadeKumar.LRHighShapeVCenteredEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeTangentAutoTree

/-!
# Centered midpoint-and-tangent pair certificates

One tangent payload generated on the singleton center supplies both target
values.  A second tangent payload on the full box supplies the six derivative
enclosures.  Each target is passed independently through the generic checked
midpoint theorem.
-/

namespace CourtadeKumar

structure LRHighShapeCenteredPairCertificate where
  center : LRHighShapeTangentCertificate
  derivative : LRHighShapeTangentCertificate

namespace LRHighShapeCenteredPairCertificate

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (derivative : LRHighShapeTangentCertificate :=
      LRHighShapeTangentCertificate.auto sqrtFuel logFuel box) :
    LRHighShapeCenteredPairCertificate :=
  { center := LRHighShapeTangentCertificate.auto
      sqrtFuel logFuel box.centerBox
    derivative := derivative }

def uPayloadCheck (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : Bool :=
  lrHighShapeInteriorBoxCheck box &&
    certificate.center.base.check box.centerBox &&
    certificate.derivative.base.check box

def uEvaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : MidpointCertificate :=
  let centerResult := certificate.center.base.evaluateAD terms box.centerBox
  let derivativeResult := certificate.derivative.base.evaluateAD terms box
  { value := centerResult.value
    derivS := derivativeResult.derivS
    derivK := derivativeResult.derivK
    derivChi := derivativeResult.derivChi }

def uAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : Bool :=
  checkedMidpointLeafAccepts uPayloadCheck (uEvaluate terms) box certificate

noncomputable def uDerivativeEnclosures (terms : ℕ)
    {box : CertificateBox}
    {certificate : LRHighShapeCenteredPairCertificate}
    (hcheck : certificate.derivative.base.check box = true)
    (hinterior : ∀ point, box.Contains point → LRHighShapeInterior point) :
    BoxDerivativeEnclosures lrCertificateUTarget box
      (certificate.uEvaluate terms box) := by
  refine
    { partialS := lrCertificateUTargetDerivS
      partialK := lrCertificateUTargetDerivK
      partialChi := lrCertificateUTargetDerivChi
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point hpoint
    exact hasDerivAt_lrCertificateUTarget_s (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateUTarget_k (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateUTarget_chi (hinterior point hpoint)
  · intro point hpoint
    have h := certificate.derivative.base.evaluateAD_sound terms hpoint hcheck
    simpa [uEvaluate] using h.2.1
  · intro point hpoint
    have h := certificate.derivative.base.evaluateAD_sound terms hpoint hcheck
    simpa [uEvaluate] using h.2.2.1
  · intro point hpoint
    have h := certificate.derivative.base.evaluateAD_sound terms hpoint hcheck
    simpa [uEvaluate] using h.2.2.2

noncomputable def uCheckedEvaluatorSound (terms : ℕ) :
    CheckedMidpointLeafEvaluatorSound lrCertificateUTarget uPayloadCheck
      (uEvaluate terms) := by
  constructor
  · intro box certificate hpayload
    have hparts :
        (lrHighShapeInteriorBoxCheck box = true ∧
          certificate.center.base.check box.centerBox = true) ∧
        certificate.derivative.base.check box = true := by
      simpa [uPayloadCheck] using hpayload
    have hcenter := certificate.center.base.evaluateAD_sound terms
      box.centerBox_contains_midpoint hparts.1.2
    simpa [uEvaluate] using hcenter.1
  · intro box certificate hpayload
    have hparts :
        (lrHighShapeInteriorBoxCheck box = true ∧
          certificate.center.base.check box.centerBox = true) ∧
        certificate.derivative.base.check box = true := by
      simpa [uPayloadCheck] using hpayload
    exact certificate.uDerivativeEnclosures terms hparts.2
      (fun _point hpoint ↦
        lrHighShapeInteriorBoxCheck_sound hparts.1.1 hpoint)

theorem u_pos_of_accepts (terms : ℕ) {box : CertificateBox}
    {certificate : LRHighShapeCenteredPairCertificate}
    (haccept : certificate.uAccepts terms box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    0 < lrCertificateUTarget point := by
  have hparts : certificate.uPayloadCheck box = true ∧
      (certificate.uEvaluate terms box).check box = true := by
    simpa [uAccepts, checkedMidpointLeafAccepts] using haccept
  exact MidpointCertificate.sound_of_derivativeEnclosures
    ((uCheckedEvaluatorSound terms).value box certificate hparts.1)
    ((uCheckedEvaluatorSound terms).derivatives box certificate hparts.1)
    hparts.2 hpoint

def tPayloadCheck (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : Bool :=
  lrHighShapeInteriorBoxCheck box &&
    certificate.center.check box.centerBox &&
    certificate.derivative.check box

def tEvaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : MidpointCertificate :=
  let centerResult := certificate.center.evaluateAD terms box.centerBox
  let derivativeResult := certificate.derivative.evaluateAD terms box
  { value := centerResult.value
    derivS := derivativeResult.derivS
    derivK := derivativeResult.derivK
    derivChi := derivativeResult.derivChi }

def tAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : Bool :=
  checkedMidpointLeafAccepts tPayloadCheck (tEvaluate terms) box certificate

noncomputable def tDerivativeEnclosures (terms : ℕ)
    {box : CertificateBox}
    {certificate : LRHighShapeCenteredPairCertificate}
    (hcheck : certificate.derivative.check box = true)
    (hinterior : ∀ point, box.Contains point → LRHighShapeInterior point) :
    BoxDerivativeEnclosures lrCertificateTTarget box
      (certificate.tEvaluate terms box) := by
  refine
    { partialS := lrCertificateTTargetDerivS
      partialK := lrCertificateTTargetDerivK
      partialChi := lrCertificateTTargetDerivChi
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point hpoint
    exact hasDerivAt_lrCertificateTTarget_s (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateTTarget_k (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateTTarget_chi (hinterior point hpoint)
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [tEvaluate] using h.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [tEvaluate] using h.2.2.1
  · intro point hpoint
    have h := certificate.derivative.evaluateAD_sound terms hpoint hcheck
    simpa [tEvaluate] using h.2.2.2

noncomputable def tCheckedEvaluatorSound (terms : ℕ) :
    CheckedMidpointLeafEvaluatorSound lrCertificateTTarget tPayloadCheck
      (tEvaluate terms) := by
  constructor
  · intro box certificate hpayload
    have hparts :
        (lrHighShapeInteriorBoxCheck box = true ∧
          certificate.center.check box.centerBox = true) ∧
        certificate.derivative.check box = true := by
      simpa [tPayloadCheck] using hpayload
    have hcenter := certificate.center.evaluateAD_sound terms
      box.centerBox_contains_midpoint hparts.1.2
    simpa [tEvaluate] using hcenter.1
  · intro box certificate hpayload
    have hparts :
        (lrHighShapeInteriorBoxCheck box = true ∧
          certificate.center.check box.centerBox = true) ∧
        certificate.derivative.check box = true := by
      simpa [tPayloadCheck] using hpayload
    exact certificate.tDerivativeEnclosures terms hparts.2
      (fun _point hpoint ↦
        lrHighShapeInteriorBoxCheck_sound hparts.1.1 hpoint)

theorem t_pos_of_accepts (terms : ℕ) {box : CertificateBox}
    {certificate : LRHighShapeCenteredPairCertificate}
    (haccept : certificate.tAccepts terms box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    0 < lrCertificateTTarget point := by
  have hparts : certificate.tPayloadCheck box = true ∧
      (certificate.tEvaluate terms box).check box = true := by
    simpa [tAccepts, checkedMidpointLeafAccepts] using haccept
  exact MidpointCertificate.sound_of_derivativeEnclosures
    ((tCheckedEvaluatorSound terms).value box certificate hparts.1)
    ((tCheckedEvaluatorSound terms).derivatives box certificate hparts.1)
    hparts.2 hpoint

def pairAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeCenteredPairCertificate) : Bool :=
  certificate.uAccepts terms box && certificate.tAccepts terms box

end LRHighShapeCenteredPairCertificate

end CourtadeKumar
