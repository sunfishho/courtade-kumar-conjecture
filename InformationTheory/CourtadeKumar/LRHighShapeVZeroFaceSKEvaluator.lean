import InformationTheory.CourtadeKumar.LRHighShapeOmegaZeroSKEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeVMidpointEvaluator

/-!
# Smooth-coordinate direct-`V` evaluator at the `χ = 0` face

This evaluator replaces exactly the two singular nodes `Q(χe)` and
`omega_s(χe)` by their endpoint-safe value/`s`/`k` evaluators.  Every other
node uses the existing checked interval-AD implementation.  Consequently
the resulting value, `s` derivative, and `k` derivative remain valid on a
closed box touching `χ = 0`; its synthetic `χ` derivative is intentionally
outside the soundness statement.
-/

namespace CourtadeKumar
namespace LRHighShapeVZeroFaceCertificate

/-- The zero-face payload strengthened only by the ordinary `Q(e)` slope
check needed for smooth derivatives. -/
def skCheck (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceCertificate) : Bool :=
  certificate.check box &&
    certificate.base.gShape.qE.check (lrCertificateEAD box).value &&
    decide ((0 : ℚ) < box.sLo ∧ (0 : ℚ) < box.kLo)

/-- Endpoint-safe interval-AD expression for the corrected direct reserve. -/
def evaluateSKAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVZeroFaceCertificate) : IntervalAD :=
  let coordinate := certificate.base.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let x := lrCertificateXAD box
  let v := coordinate.vAD box
  let onePlusV := IntervalAD.add (IntervalAD.const 1) v
  let m := IntervalAD.divPositive v onePlusV
  let ab := certificate.base.ab.evaluate terms box coordinate
  let g0 := certificate.base.gShape.g0.evaluate terms v
  let qY0 := certificate.qY0.evaluateY0SK terms box
  let qE := certificate.base.gShape.qE.evaluate terms e
  let g := IntervalAD.add (IntervalAD.add g0 qY0)
    (IntervalAD.divPositive qE v)
  let w := certificate.base.kernel.omegaZero.evaluate terms s
  let omegaY0 := certificate.omegaY0.evaluateY0SK terms box
  let omegaE := certificate.base.kernel.omegaE.evaluate terms s e
  let pw := IntervalAD.add omegaY0 (IntervalAD.divPositive omegaE v)
  let p := IntervalAD.mul m (IntervalAD.const (1 / 2))
  let bracket := IntervalAD.add
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) p) ab.d)
    (IntervalAD.mul (IntervalAD.mul p x) ab.b)
  let half := IntervalAD.sub
    (IntervalAD.add (IntervalAD.mul ab.d g) (IntervalAD.mul ab.a pw))
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) bracket)
  let j := IntervalAD.sub (IntervalAD.mul ab.b x) ab.d
  IntervalAD.sub half
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 2) w) m) j)

/-- Soundness of the value and two smooth derivative fields of
`evaluateSKAD`. -/
theorem evaluateSKAD_sound (terms : ℕ) {box : CertificateBox}
    {certificate : LRHighShapeVZeroFaceCertificate}
    (hcheck : certificate.skCheck box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    let result := certificate.evaluateSKAD terms box
    result.value.Contains (lrCertificateVTarget point) ∧
      result.derivS.Contains (lrCertificateVTargetDerivS point) ∧
      result.derivK.Contains (lrCertificateVTargetDerivK point) := by
  dsimp only
  let coordinate := certificate.base.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0NonnegativeAD box
  let x := lrCertificateXAD box
  let v := coordinate.vAD box
  let onePlusV := IntervalAD.add (IntervalAD.const 1) v
  let m := IntervalAD.divPositive v onePlusV
  let ab := certificate.base.ab.evaluate terms box coordinate
  let g0 := certificate.base.gShape.g0.evaluate terms v
  let qY0 := certificate.qY0.evaluateY0SK terms box
  let qE := certificate.base.gShape.qE.evaluate terms e
  let g := IntervalAD.add (IntervalAD.add g0 qY0)
    (IntervalAD.divPositive qE v)
  let w := certificate.base.kernel.omegaZero.evaluate terms s
  let omegaY0 := certificate.omegaY0.evaluateY0SK terms box
  let omegaE := certificate.base.kernel.omegaE.evaluate terms s e
  let pw := IntervalAD.add omegaY0 (IntervalAD.divPositive omegaE v)
  let p := IntervalAD.mul m (IntervalAD.const (1 / 2))
  let bracket := IntervalAD.add
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) p) ab.d)
    (IntervalAD.mul (IntervalAD.mul p x) ab.b)
  let half := IntervalAD.sub
    (IntervalAD.add (IntervalAD.mul ab.d g) (IntervalAD.mul ab.a pw))
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) bracket)
  let j := IntervalAD.sub (IntervalAD.mul ab.b x) ab.d
  have hchecks :
      (certificate.check box = true ∧
        certificate.base.gShape.qE.check e.value = true) ∧
      decide ((0 : ℚ) < box.sLo ∧ (0 : ℚ) < box.kLo) = true := by
    simpa [skCheck, e] using hcheck
  have hchecked :
      decide ((0 : ℚ) ≤ box.chiLo ∧ (0 : ℚ) ≤ e.value.lower) = true ∧
      decide (
        coordinate.check box = true ∧
        certificate.base.kernel.omegaZero.check s = true ∧
        certificate.omegaY0.check s y0 = true ∧
        certificate.base.kernel.omegaE.check s e = true ∧
        certificate.base.gShape.g0.check v = true ∧
        certificate.qY0.check y0.value = true ∧
        certificate.base.gShape.qE.value.check e.value = true ∧
        certificate.base.ab.check box coordinate = true ∧
        (0 : ℚ) < v.value.lower) = true := by
    simpa [LRHighShapeVZeroFaceCertificate.check, coordinate, s, e, y0, v]
      using hchecks.1.1
  have hdomain : (0 : ℚ) ≤ box.chiLo ∧
      (0 : ℚ) ≤ e.value.lower := by
    simpa using hchecked.1
  have hparts :
      coordinate.check box = true ∧
      certificate.base.kernel.omegaZero.check s = true ∧
      certificate.omegaY0.check s y0 = true ∧
      certificate.base.kernel.omegaE.check s e = true ∧
      certificate.base.gShape.g0.check v = true ∧
      certificate.qY0.check y0.value = true ∧
      certificate.base.gShape.qE.value.check e.value = true ∧
      certificate.base.ab.check box coordinate = true ∧
      (0 : ℚ) < v.value.lower := by
    simpa using hchecked.2
  have hsk : (0 : ℚ) < box.sLo ∧ (0 : ℚ) < box.kLo := by
    simpa using hchecks.2
  have hsPos : (0 : ℚ) < box.sLo := hsk.1
  have hkPos : (0 : ℚ) < box.kLo := hsk.2
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have heSound := lrCertificateEAD_sound hpoint
  have hy0Sound := lrCertificateY0NonnegativeAD_sound hpoint
    hdomain.1 hdomain.2
  have hxSound := lrCertificateXAD_sound hpoint
  have hv := coordinate.vAD_sound hpoint hparts.1
  have hab := certificate.base.ab.sound terms hpoint hparts.2.2.2.2.2.2.2.1
  have hg0 := certificate.base.gShape.g0.sound terms hparts.2.2.2.2.1 hv
  have hqY0Parts := certificate.qY0.evaluateY0SK_sound terms
    hparts.2.2.2.2.2.1 hsPos hkPos hdomain.1 hdomain.2 hpoint
  have hqY0 : qY0.Contains
      (lrCertificateQ (lrCertificateY0 point))
      (lrCertificateQPrime (lrCertificateY0 point) *
        lrCertificateY0DerivS point)
      (lrCertificateQPrime (lrCertificateY0 point) *
        lrCertificateY0DerivK point) 0 := by
    refine ⟨hqY0Parts.1, hqY0Parts.2.1, hqY0Parts.2.2, ?_⟩
    simp [qY0, LRQZeroIntervalCertificate.evaluateY0SK,
      RationalEnclosure.point, RationalEnclosure.Contains]
  have hqE := certificate.base.gShape.qE.sound terms hchecks.1.2 heSound
  have hqEdiv := IntervalAD.contains_divPositive
    hparts.2.2.2.2.2.2.2.2 hqE hv
  have hg := IntervalAD.contains_add
    (IntervalAD.contains_add hg0 hqY0) hqEdiv
  have hw := certificate.base.kernel.omegaZero.sound terms hparts.2.1 hs
  rcases certificate.omegaY0.evaluateY0SK_sound terms
      hparts.2.2.1 hsPos hkPos hdomain.1 hdomain.2 hpoint with
    ⟨omegaY0Chi, homegaY0⟩
  have homegaE := certificate.base.kernel.omegaE.sound terms
    hparts.2.2.2.1 hs heSound
  have homegaEdiv := IntervalAD.contains_divPositive
    hparts.2.2.2.2.2.2.2.2 homegaE hv
  have hpw := IntervalAD.contains_add homegaY0 homegaEdiv
  let gChi :=
    lrCertificateG0Prime (lrCertificateV point) *
        lrCertificateVDerivChi point + 0 +
      (lrCertificateQPrime (lrCertificateE point) *
          lrCertificateEDerivChi point * lrCertificateV point -
        lrCertificateQ (lrCertificateE point) *
          lrCertificateVDerivChi point) / lrCertificateV point ^ 2
  have hgNamed : g.Contains (lrCertificateGShape point)
      (lrCertificateGShapeDerivS point)
      (lrCertificateGShapeDerivK point) gChi := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [g, lrCertificateGShape, lrCertificateGShapeValue] using hg.1
    · simpa [g, lrCertificateGShapeDerivS, lrCertificateGShapeDeriv,
        lrCertificateGShapeValueDeriv] using hg.2.1
    · simpa [g, lrCertificateGShapeDerivK, lrCertificateGShapeDeriv,
        lrCertificateGShapeValueDeriv] using hg.2.2.1
    · simpa [g, gChi] using hg.2.2.2
  let pwChi := omegaY0Chi +
    (lrCertificateOmegaDeriv point.s (lrCertificateE point) 0
          (lrCertificateEDerivChi point) * lrCertificateV point -
        lrCertificateOmega point.s (lrCertificateE point) *
          lrCertificateVDerivChi point) / lrCertificateV point ^ 2
  have hpwNamed : pw.Contains (lrCertificatePW point)
      (lrCertificatePWDerivS point) (lrCertificatePWDerivK point)
      pwChi := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [pw, lrCertificatePW, lrCertificatePWValue] using hpw.1
    · simpa [pw, lrCertificatePWDerivS, lrCertificatePWDeriv,
        lrCertificatePWValueDeriv] using hpw.2.1
    · simpa [pw, lrCertificatePWDerivK, lrCertificatePWDeriv,
        lrCertificatePWValueDeriv] using hpw.2.2.1
    · simpa [pw, pwChi] using hpw.2.2.2
  have honePlusV := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have honePlusVPos : (0 : ℚ) < onePlusV.value.lower := by
    change 0 < 1 + v.value.lower
    linarith [hparts.2.2.2.2.2.2.2.2]
  have hm := IntervalAD.contains_divPositive honePlusVPos hv honePlusV
  have hvPointPos : 0 < lrCertificateV point := by
    have hvLo : (0 : ℝ) < (v.value.lower : ℝ) := by
      exact_mod_cast hparts.2.2.2.2.2.2.2.2
    exact hvLo.trans_le hv.1.1
  have hvPlusNe : 1 + lrCertificateV point ≠ 0 := by linarith
  have hmNamed : m.Contains (lrCertificateM point)
      (lrCertificateMDeriv point (lrCertificateVDerivS point))
      (lrCertificateMDeriv point (lrCertificateVDerivK point))
      (lrCertificateMDeriv point (lrCertificateVDerivChi point)) := by
    convert hm using 1 <;>
      simp [m, lrCertificateM, lrCertificateMDeriv] <;>
      field_simp [hvPlusNe] <;> ring
  have hp := IntervalAD.contains_mul hmNamed
    (IntervalAD.contains_const (1 / 2))
  have honeMinusP := IntervalAD.contains_sub (IntervalAD.contains_const 1) hp
  have hleft := IntervalAD.contains_mul honeMinusP hab.2.2
  have hpx := IntervalAD.contains_mul hp hxSound
  have hright := IntervalAD.contains_mul hpx hab.2.1
  have hbracketRaw := IntervalAD.contains_add hleft hright
  have hbracket : bracket.Contains (lrCertificateHalfMidpointBracket point)
      (lrCertificateHalfMidpointBracketDeriv point
        (lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
          (lrCertificateVDerivS point))
        (lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
          (lrCertificateVDerivS point))
        (lrCertificateMDeriv point (lrCertificateVDerivS point))
        (lrCertificateXDerivS point))
      (lrCertificateHalfMidpointBracketDeriv point
        (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
          (lrCertificateVDerivK point))
        (lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
          (lrCertificateVDerivK point))
        (lrCertificateMDeriv point (lrCertificateVDerivK point))
        (lrCertificateXDerivK point))
      (lrCertificateHalfMidpointBracketDeriv point
        (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
          (lrCertificateVDerivChi point))
        (lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
          (lrCertificateVDerivChi point))
        (lrCertificateMDeriv point (lrCertificateVDerivChi point))
        (lrCertificateXDerivChi point)) := by
    convert hbracketRaw using 1 <;>
      simp [bracket, lrCertificateHalfMidpointBracket,
        lrCertificateHalfMidpointBracketDeriv] <;> ring
  have hpositive := IntervalAD.contains_add
    (IntervalAD.contains_mul hab.2.2 hgNamed)
    (IntervalAD.contains_mul hab.1 hpwNamed)
  have hhalfCorrection := IntervalAD.contains_mul
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw) hbracket
  have hhalfRaw := IntervalAD.contains_sub hpositive hhalfCorrection
  let halfChi :=
    (lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
          (lrCertificateVDerivChi point) * lrCertificateGShape point +
        lrCertificateD point * gChi +
      (lrCertificateADeriv point (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point) * lrCertificatePW point +
        lrCertificateA point * pwChi)) -
      ((0 * lrCertificateOmega point.s 0 +
            4 * lrCertificateOmegaDeriv point.s 0 0 0) *
          lrCertificateHalfMidpointBracket point +
        4 * lrCertificateOmega point.s 0 *
          lrCertificateHalfMidpointBracketDeriv point
            (lrCertificateBFlowDeriv point 0
              (lrCertificateEDerivChi point)
              (lrCertificateVDerivChi point))
            (lrCertificateDDeriv point 0
              (lrCertificateEDerivChi point)
              (lrCertificateVDerivChi point))
            (lrCertificateMDeriv point (lrCertificateVDerivChi point))
            (lrCertificateXDerivChi point))
  have hhalf : half.Contains (lrCertificateHalfMidpointNumerator point)
      (lrCertificateHalfMidpointNumeratorDeriv point
        (lrCertificateADeriv point (lrCertificateEDerivS point)
          (lrCertificateVDerivS point))
        (lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
          (lrCertificateVDerivS point))
        (lrCertificateGShapeDerivS point)
        (lrCertificateOmegaDeriv point.s 0 1 0)
        (lrCertificatePWDerivS point)
        (lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
          (lrCertificateVDerivS point))
        (lrCertificateMDeriv point (lrCertificateVDerivS point))
        (lrCertificateXDerivS point))
      (lrCertificateHalfMidpointNumeratorDeriv point
        (lrCertificateADeriv point (lrCertificateEDerivK point)
          (lrCertificateVDerivK point))
        (lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
          (lrCertificateVDerivK point))
        (lrCertificateGShapeDerivK point)
        (lrCertificateOmegaDeriv point.s 0 0 0)
        (lrCertificatePWDerivK point)
        (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
          (lrCertificateVDerivK point))
        (lrCertificateMDeriv point (lrCertificateVDerivK point))
        (lrCertificateXDerivK point)) halfChi := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [half, lrCertificateHalfMidpointNumerator] using hhalfRaw.1
    · convert hhalfRaw.2.1 using 1 <;>
        simp [half, lrCertificateW,
          lrCertificateHalfMidpointNumeratorDeriv] <;> ring
    · convert hhalfRaw.2.2.1 using 1 <;>
        simp [half, lrCertificateW,
          lrCertificateHalfMidpointNumeratorDeriv] <;> ring
    · simpa [half, halfChi] using hhalfRaw.2.2.2
  have hjRaw := IntervalAD.contains_sub
    (IntervalAD.contains_mul hab.2.1 hxSound) hab.2.2
  have hj : j.Contains (lrCertificateJ point)
      (lrCertificateJDeriv point
        (lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
          (lrCertificateVDerivS point))
        (lrCertificateXDerivS point)
        (lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
          (lrCertificateVDerivS point)))
      (lrCertificateJDeriv point
        (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
          (lrCertificateVDerivK point))
        (lrCertificateXDerivK point)
        (lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
          (lrCertificateVDerivK point)))
      (lrCertificateJDeriv point
        (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
          (lrCertificateVDerivChi point))
        (lrCertificateXDerivChi point)
        (lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
          (lrCertificateVDerivChi point))) := by
    convert hjRaw using 1 <;>
      simp [j, lrCertificateJ, lrCertificateJDeriv] <;> ring
  have hcorrection := IntervalAD.contains_mul
    (IntervalAD.contains_mul
      (IntervalAD.contains_mul (IntervalAD.contains_const 2) hw) hmNamed) hj
  let result := IntervalAD.sub half
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 2) w) m) j)
  have hresult := IntervalAD.contains_sub hhalf hcorrection
  change result.value.Contains (lrCertificateVTarget point) ∧
    result.derivS.Contains (lrCertificateVTargetDerivS point) ∧
    result.derivK.Contains (lrCertificateVTargetDerivK point)
  refine ⟨?_, ?_, ?_⟩
  · rw [lrCertificateVTarget_eq_halfMidpoint_sub]
    simpa [result] using hresult.1
  · convert hresult.2.1 using 1 <;>
      simp [result, lrCertificateVTargetDerivS,
        lrCertificateVTargetCurveDeriv, lrCertificateVTargetDeriv,
        lrCertificateHalfMidpointNumeratorCurveDeriv,
        lrCertificateEDerivS, lrCertificateXDerivS,
        lrCertificateY0DerivS, lrCertificateVDerivS,
        lrCertificateGShapeDerivS,
        lrCertificatePWDerivS,
        lrCertificateW] <;> ring
  · convert hresult.2.2.1 using 1 <;>
      simp [result, lrCertificateVTargetDerivK,
        lrCertificateVTargetCurveDeriv, lrCertificateVTargetDeriv,
        lrCertificateHalfMidpointNumeratorCurveDeriv,
        lrCertificateEDerivK, lrCertificateXDerivK,
        lrCertificateY0DerivK, lrCertificateVDerivK,
        lrCertificateGShapeDerivK,
        lrCertificatePWDerivK,
        lrCertificateW] <;> ring

end LRHighShapeVZeroFaceCertificate
end CourtadeKumar
