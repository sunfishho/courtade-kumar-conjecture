import InformationTheory.CourtadeKumar.LRCertificateOmegaZeroInterval

/-!
# Value-only direct-`V` evaluator on the `χ = 0` face

Only the nodes `Q(χe)` and `omega_s(χe)` are singular in derivative form.
The direct reserve needs values, not their derivatives.  This evaluator
therefore reuses the regular high-shape payload everywhere else and swaps in
the zero-endpoint value certificates exactly at those two nodes.
-/

namespace CourtadeKumar

structure LRHighShapeVZeroFaceCertificate where
  base : LRHighShapeVCertificate
  qY0 : LRQZeroIntervalCertificate
  omegaY0 : LROmegaZeroIntervalCertificate

namespace LRHighShapeVZeroFaceCertificate

def check (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceCertificate) : Bool :=
  let coordinate := certificate.base.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let v := coordinate.vAD box
  decide (
    coordinate.check box = true ∧
    certificate.base.kernel.omegaZero.check s = true ∧
    certificate.omegaY0.check s y0 = true ∧
    certificate.base.kernel.omegaE.check s e = true ∧
    certificate.base.gShape.g0.check v = true ∧
    certificate.qY0.check y0.value = true ∧
    certificate.base.gShape.qE.value.check e.value = true ∧
    certificate.base.ab.check box coordinate = true ∧
    (0 : ℚ) < v.value.lower)

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceCertificate) : RationalEnclosure :=
  let coordinate := certificate.base.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let x := (lrCertificateXAD box).value
  let v := (coordinate.vAD box).value
  let onePlusV := RationalEnclosure.add (RationalEnclosure.point 1) v
  let m := RationalEnclosure.div v onePlusV
  let ab := certificate.base.ab.evaluate terms box coordinate
  let g0 := (certificate.base.gShape.g0.evaluate terms
    (coordinate.vAD box)).value
  let qY0 := certificate.qY0.enclosure terms y0.value
  let qE := certificate.base.gShape.qE.value.enclosure terms
  let g := RationalEnclosure.add (RationalEnclosure.add g0 qY0)
    (RationalEnclosure.div qE v)
  let w := (certificate.base.kernel.omegaZero.evaluate terms s).value
  let omegaY0 := certificate.omegaY0.evaluate terms s y0
  let omegaE := (certificate.base.kernel.omegaE.evaluate terms s e).value
  let pw := RationalEnclosure.add omegaY0
    (RationalEnclosure.div omegaE v)
  let p := RationalEnclosure.mul m (RationalEnclosure.point (1 / 2))
  let bracket := RationalEnclosure.add
    (RationalEnclosure.mul
      (RationalEnclosure.sub (RationalEnclosure.point 1) p) ab.d.value)
    (RationalEnclosure.mul (RationalEnclosure.mul p x) ab.b.value)
  let half := RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.mul ab.d.value g)
      (RationalEnclosure.mul ab.a.value pw))
    (RationalEnclosure.mul
      (RationalEnclosure.mul (RationalEnclosure.point 4) w) bracket)
  let j := RationalEnclosure.sub
    (RationalEnclosure.mul ab.b.value x) ab.d.value
  RationalEnclosure.sub half
    (RationalEnclosure.mul
      (RationalEnclosure.mul
        (RationalEnclosure.mul (RationalEnclosure.point 2) w) m) j)

theorem evaluate_sound (terms : ℕ) {box : CertificateBox}
    {certificate : LRHighShapeVZeroFaceCertificate}
    (hcheck : certificate.check box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (certificate.evaluate terms box).Contains (lrCertificateVTarget point) := by
  let coordinate := certificate.base.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let x := (lrCertificateXAD box).value
  let v := (coordinate.vAD box).value
  let ab := certificate.base.ab.evaluate terms box coordinate
  have hparts :
      coordinate.check box = true ∧
      certificate.base.kernel.omegaZero.check s = true ∧
      certificate.omegaY0.check s y0 = true ∧
      certificate.base.kernel.omegaE.check s e = true ∧
      certificate.base.gShape.g0.check (coordinate.vAD box) = true ∧
      certificate.qY0.check y0.value = true ∧
      certificate.base.gShape.qE.value.check e.value = true ∧
      certificate.base.ab.check box coordinate = true ∧
      (0 : ℚ) < v.lower := by
    simpa [check, coordinate, s, e, y0, v] using hcheck
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have he := lrCertificateEAD_sound hpoint
  have hy0 := lrCertificateY0AD_sound hpoint
  have hx := lrCertificateXAD_sound hpoint
  have hvAD := coordinate.vAD_sound hpoint hparts.1
  have hv : v.Contains (lrCertificateV point) := by
    simpa [v] using hvAD.1
  have hab := certificate.base.ab.sound terms hpoint hparts.2.2.2.2.2.2.2.1
  have hg0AD := certificate.base.gShape.g0.sound terms
    hparts.2.2.2.2.1 hvAD
  have hg0 := hg0AD.1
  have hqY0 := certificate.qY0.sound terms hparts.2.2.2.2.2.1 hy0.1
  have hqE := certificate.base.gShape.qE.value.sound terms
    hparts.2.2.2.2.2.2.1 he.1
  have hqEdiv := RationalEnclosure.contains_div hparts.2.2.2.2.2.2.2.2
    hqE hv
  have hg := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add hg0 hqY0) hqEdiv
  have hwAD := certificate.base.kernel.omegaZero.sound terms hparts.2.1 hs
  have hw := hwAD.1
  have homegaY0 := certificate.omegaY0.sound terms hparts.2.2.1 hs hy0
  have homegaEAD := certificate.base.kernel.omegaE.sound terms
    hparts.2.2.2.1 hs he
  have homegaE := homegaEAD.1
  have homegaEdiv := RationalEnclosure.contains_div
    hparts.2.2.2.2.2.2.2.2 homegaE hv
  have hpw := RationalEnclosure.contains_add homegaY0 homegaEdiv
  let onePlusV := RationalEnclosure.add (RationalEnclosure.point 1) v
  have honePlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hv
  have honePlusVPos : (0 : ℚ) < onePlusV.lower := by
    change 0 < 1 + v.lower
    linarith [hparts.2.2.2.2.2.2.2.2]
  have hm := RationalEnclosure.contains_div honePlusVPos hv honePlusV
  have hp := RationalEnclosure.contains_mul hm
    (RationalEnclosure.contains_point (1 / 2))
  have honeMinusP := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hp
  have ha : ab.a.value.Contains (lrCertificateA point) := by
    simpa [ab] using hab.1.1
  have hb : ab.b.value.Contains (lrCertificateBFlow point) := by
    simpa [ab] using hab.2.1.1
  have hd : ab.d.value.Contains (lrCertificateD point) := by
    simpa [ab] using hab.2.2.1
  have hleft := RationalEnclosure.contains_mul honeMinusP hd
  have hpx := RationalEnclosure.contains_mul hp hx.1
  have hright := RationalEnclosure.contains_mul hpx hb
  have hbracket := RationalEnclosure.contains_add hleft hright
  have hpositive := RationalEnclosure.contains_add
    (RationalEnclosure.contains_mul hd hg)
    (RationalEnclosure.contains_mul ha hpw)
  have hhalfCorrection := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point 4) hw) hbracket
  have hhalf := RationalEnclosure.contains_sub hpositive hhalfCorrection
  have hj := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_mul hb hx.1) hd
  have hcorrection := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 2) hw) hm) hj
  have hresult := RationalEnclosure.contains_sub hhalf hcorrection
  rw [lrCertificateVTarget_eq_halfMidpoint_sub]
  simpa [evaluate, coordinate, s, e, y0, x, v, ab, onePlusV,
    lrCertificateHalfMidpointNumerator,
    lrCertificateHalfMidpointBracket, lrCertificateJ,
    lrCertificateGShape, lrCertificateGShapeValue,
    lrCertificatePW, lrCertificatePWValue] using hresult

def payloadCheck (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceCertificate) : Bool :=
  certificate.check box

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceCertificate) : Bool :=
  checkedEnclosureLeafAccepts payloadCheck (evaluate terms) box certificate

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound lrCertificateVTarget payloadCheck
      (evaluate terms) := by
  constructor
  intro box certificate hpayload point hpoint
  exact certificate.evaluate_sound terms (by
    simpa [payloadCheck] using hpayload) hpoint

def autoFromBase (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (base : LRHighShapeVCertificate) : LRHighShapeVZeroFaceCertificate :=
  let s := lrCertificateSAD box
  let y0 := lrCertificateY0AD box
  { base := base
    qY0 := LRQZeroIntervalCertificate.auto sqrtFuel logFuel y0.value
    omegaY0 := LROmegaZeroIntervalCertificate.auto sqrtFuel logFuel s y0 }

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRHighShapeVZeroFaceCertificate :=
  autoFromBase sqrtFuel logFuel box
    (LRHighShapeVCertificate.auto sqrtFuel logFuel box)

end LRHighShapeVZeroFaceCertificate

/-- End-to-end soundness for a subdivision whose accepted leaves use the
value-only evaluator valid on boxes touching the `χ = 0` face. -/
theorem lrHighShapeVZeroFaceSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeVZeroFaceCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeVZeroFaceCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateVTarget point := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    (LRHighShapeVZeroFaceCertificate.checkedEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

end CourtadeKumar
