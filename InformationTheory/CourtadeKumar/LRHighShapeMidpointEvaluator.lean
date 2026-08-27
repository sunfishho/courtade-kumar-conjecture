import InformationTheory.CourtadeKumar.LRHighShapeABAssembly
import InformationTheory.CourtadeKumar.IntervalCertificateAssembly

/-!
# Verified evaluator for the high-shape half-midpoint target

This module assembles the checked interval-AD nodes for the exact numerator
`N(M/2)` and divides by the manuscript normalization `s * e`.  The assembly
uses the cancellation-safe coordinates `e`, `x`, `A`, `B`, `D`, `G`, `W`, and
`P_W`; it is subsequently identified with `lrHighShapeUCertificateTarget`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrCertificateM (point : CertificatePoint) : ℝ :=
  lrCertificateV point / (1 + lrCertificateV point)

noncomputable def lrCertificateMDeriv
    (point : CertificatePoint) (v' : ℝ) : ℝ :=
  v' / (1 + lrCertificateV point) ^ 2

noncomputable def lrCertificateHalfMidpointBracket
    (point : CertificatePoint) : ℝ :=
  let p := lrCertificateM point / 2
  (1 - p) * lrCertificateD point +
    p * lrCertificateX point * lrCertificateBFlow point

noncomputable def lrCertificateHalfMidpointBracketDeriv
    (point : CertificatePoint) (b' d' m' x' : ℝ) : ℝ :=
  let p := lrCertificateM point / 2
  let p' := m' / 2
  (-p') * lrCertificateD point + (1 - p) * d' +
    (p' * lrCertificateX point + p * x') * lrCertificateBFlow point +
    (p * lrCertificateX point) * b'

noncomputable def lrCertificateHalfMidpointNumerator
    (point : CertificatePoint) : ℝ :=
  lrCertificateD point * lrCertificateGShape point +
    lrCertificateA point * lrCertificatePW point -
    4 * lrCertificateW point * lrCertificateHalfMidpointBracket point

noncomputable def lrCertificateHalfMidpointNumeratorDeriv
    (point : CertificatePoint)
    (a' d' g' w' pw' b' m' x' : ℝ) : ℝ :=
  d' * lrCertificateGShape point + lrCertificateD point * g' +
    (a' * lrCertificatePW point + lrCertificateA point * pw') -
    4 * (w' * lrCertificateHalfMidpointBracket point +
      lrCertificateW point *
        lrCertificateHalfMidpointBracketDeriv point b' d' m' x')

def lrCertificateUDenominator (point : CertificatePoint) : ℝ :=
  point.s * lrCertificateE point

def lrCertificateUDenominatorDeriv
    (point : CertificatePoint) (s' e' : ℝ) : ℝ :=
  s' * lrCertificateE point + point.s * e'

noncomputable def lrCertificateUTarget (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumerator point /
    lrCertificateUDenominator point

noncomputable def lrCertificateUTargetDeriv
    (point : CertificatePoint) (numerator' denominator' : ℝ) : ℝ :=
  (numerator' * lrCertificateUDenominator point -
      lrCertificateHalfMidpointNumerator point * denominator') /
    lrCertificateUDenominator point ^ 2

private noncomputable def lrCertificateADerivS (point : CertificatePoint) : ℝ :=
  lrCertificateADeriv point (lrCertificateEDerivS point)
    (lrCertificateVDerivS point)

private noncomputable def lrCertificateADerivK (point : CertificatePoint) : ℝ :=
  lrCertificateADeriv point (lrCertificateEDerivK point)
    (lrCertificateVDerivK point)

private noncomputable def lrCertificateADerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateADeriv point (lrCertificateEDerivChi point)
    (lrCertificateVDerivChi point)

private noncomputable def lrCertificateBFlowDerivS
    (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
    (lrCertificateVDerivS point)

private noncomputable def lrCertificateBFlowDerivK
    (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
    (lrCertificateVDerivK point)

private noncomputable def lrCertificateBFlowDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
    (lrCertificateVDerivChi point)

private noncomputable def lrCertificateDDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
    (lrCertificateVDerivS point)

private noncomputable def lrCertificateDDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
    (lrCertificateVDerivK point)

private noncomputable def lrCertificateDDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
    (lrCertificateVDerivChi point)

noncomputable def lrCertificateHalfMidpointNumeratorDerivS
    (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADerivS point) (lrCertificateDDerivS point)
    (lrCertificateGShapeDerivS point) (lrCertificateWDerivS point)
    (lrCertificatePWDerivS point) (lrCertificateBFlowDerivS point)
    (lrCertificateMDeriv point (lrCertificateVDerivS point))
    (lrCertificateXDerivS point)

noncomputable def lrCertificateHalfMidpointNumeratorDerivK
    (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADerivK point) (lrCertificateDDerivK point)
    (lrCertificateGShapeDerivK point) (lrCertificateWDerivK point)
    (lrCertificatePWDerivK point) (lrCertificateBFlowDerivK point)
    (lrCertificateMDeriv point (lrCertificateVDerivK point))
    (lrCertificateXDerivK point)

noncomputable def lrCertificateHalfMidpointNumeratorDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADerivChi point) (lrCertificateDDerivChi point)
    (lrCertificateGShapeDerivChi point) (lrCertificateWDerivChi point)
    (lrCertificatePWDerivChi point) (lrCertificateBFlowDerivChi point)
    (lrCertificateMDeriv point (lrCertificateVDerivChi point))
    (lrCertificateXDerivChi point)

noncomputable def lrCertificateUTargetDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateUTargetDeriv point
    (lrCertificateHalfMidpointNumeratorDerivS point)
    (lrCertificateUDenominatorDeriv point 1 (lrCertificateEDerivS point))

noncomputable def lrCertificateUTargetDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateUTargetDeriv point
    (lrCertificateHalfMidpointNumeratorDerivK point)
    (lrCertificateUDenominatorDeriv point 0 (lrCertificateEDerivK point))

noncomputable def lrCertificateUTargetDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateUTargetDeriv point
    (lrCertificateHalfMidpointNumeratorDerivChi point)
    (lrCertificateUDenominatorDeriv point 0 (lrCertificateEDerivChi point))

/-- All untrusted scalar payloads needed at one accepted midpoint leaf. -/
structure LRHighShapeMidpointCertificate where
  kernel : LRHighShapeKernelCertificate
  gShape : LRHighShapeGCertificate
  ab : LRHighShapeABCertificate

namespace LRHighShapeMidpointCertificate

def mAD (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : IntervalAD :=
  let v := certificate.kernel.coordinate.vAD box
  IntervalAD.divPositive v (IntervalAD.add (IntervalAD.const 1) v)

def numeratorAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : IntervalAD :=
  let coordinate := certificate.kernel.coordinate
  let ab := certificate.ab.evaluate terms box coordinate
  let g := certificate.gShape.evaluate terms box coordinate
  let w := certificate.kernel.wAD terms box
  let pw := certificate.kernel.pwAD terms box
  let p := IntervalAD.mul (certificate.mAD box) (IntervalAD.const (1 / 2))
  let bracket := IntervalAD.add
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) p) ab.d)
    (IntervalAD.mul (IntervalAD.mul p (lrCertificateXAD box)) ab.b)
  IntervalAD.sub
    (IntervalAD.add (IntervalAD.mul ab.d g) (IntervalAD.mul ab.a pw))
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) bracket)

def denominatorAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul (lrCertificateSAD box) (lrCertificateEAD box)

def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : IntervalAD :=
  IntervalAD.divPositive (certificate.numeratorAD terms box)
    (denominatorAD box)

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : MidpointCertificate :=
  let result := certificate.evaluateAD terms box
  { value := result.value
    derivS := result.derivS
    derivK := result.derivK
    derivChi := result.derivChi }

def check (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : Bool :=
  let coordinate := certificate.kernel.coordinate
  let v := coordinate.vAD box
  decide (
    certificate.kernel.check box = true ∧
    certificate.gShape.check box coordinate = true ∧
    certificate.ab.check box coordinate = true ∧
    (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
    (0 : ℚ) < (denominatorAD box).value.lower)

theorem mAD_sound {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.mAD box).Contains (lrCertificateM point)
      (lrCertificateMDeriv point (lrCertificateVDerivS point))
      (lrCertificateMDeriv point (lrCertificateVDerivK point))
      (lrCertificateMDeriv point (lrCertificateVDerivChi point)) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) < (denominatorAD box).value.lower := by
    simpa [check] using hcheck
  have hkernelParts :
      certificate.kernel.coordinate.check box = true ∧
      certificate.kernel.omegaZero.check (lrCertificateSAD box)
        (IntervalAD.const 0) = true ∧
      certificate.kernel.omegaY0.check (lrCertificateSAD box)
        (lrCertificateY0AD box) = true ∧
      certificate.kernel.omegaE.check (lrCertificateSAD box)
        (lrCertificateEAD box) = true ∧
      (0 : ℚ) < (certificate.kernel.coordinate.vAD box).value.lower := by
    simpa [LRHighShapeKernelCertificate.check] using hparts.1
  have hv := certificate.kernel.coordinate.vAD_sound hpoint hkernelParts.1
  have honePlus := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have h := IntervalAD.contains_divPositive hparts.2.2.2.1 hv honePlus
  unfold mAD lrCertificateM lrCertificateMDeriv
  dsimp only
  convert h using 1 <;> field_simp <;> ring

theorem numeratorAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.numeratorAD terms box).Contains
      (lrCertificateHalfMidpointNumerator point)
      (lrCertificateHalfMidpointNumeratorDerivS point)
      (lrCertificateHalfMidpointNumeratorDerivK point)
      (lrCertificateHalfMidpointNumeratorDerivChi point) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) < (denominatorAD box).value.lower := by
    simpa [check] using hcheck
  have hab := certificate.ab.sound terms hpoint hparts.2.2.1
  have hg := certificate.gShape.sound terms hpoint hparts.2.1
  have hw := certificate.kernel.wAD_sound terms hpoint hparts.1
  have hpw := certificate.kernel.pwAD_sound terms hpoint hparts.1
  have hm := certificate.mAD_sound hpoint hcheck
  have hx := lrCertificateXAD_sound hpoint
  have hp := IntervalAD.contains_mul hm (IntervalAD.contains_const (1 / 2))
  have honeMinusP := IntervalAD.contains_sub (IntervalAD.contains_const 1) hp
  have hleft := IntervalAD.contains_mul honeMinusP hab.2.2
  have hpx := IntervalAD.contains_mul hp hx
  have hright := IntervalAD.contains_mul hpx hab.2.1
  have hbracket := IntervalAD.contains_add hleft hright
  have hdg := IntervalAD.contains_mul hab.2.2 hg
  have hapw := IntervalAD.contains_mul hab.1 hpw
  have hpositive := IntervalAD.contains_add hdg hapw
  have h4w := IntervalAD.contains_mul
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw) hbracket
  have h := IntervalAD.contains_sub hpositive h4w
  unfold numeratorAD lrCertificateHalfMidpointNumerator
    lrCertificateHalfMidpointNumeratorDerivS
    lrCertificateHalfMidpointNumeratorDerivK
    lrCertificateHalfMidpointNumeratorDerivChi
    lrCertificateHalfMidpointNumeratorDeriv
    lrCertificateHalfMidpointBracket
    lrCertificateHalfMidpointBracketDeriv
    lrCertificateADerivS lrCertificateADerivK lrCertificateADerivChi
    lrCertificateBFlowDerivS lrCertificateBFlowDerivK
    lrCertificateBFlowDerivChi lrCertificateDDerivS
    lrCertificateDDerivK lrCertificateDDerivChi
  dsimp only
  convert h using 1 <;> ring

theorem denominatorAD_sound {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    (denominatorAD box).Contains (lrCertificateUDenominator point)
      (lrCertificateUDenominatorDeriv point 1 (lrCertificateEDerivS point))
      (lrCertificateUDenominatorDeriv point 0 (lrCertificateEDerivK point))
      (lrCertificateUDenominatorDeriv point 0
        (lrCertificateEDerivChi point)) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have h := IntervalAD.contains_mul hs (lrCertificateEAD_sound hpoint)
  simpa [denominatorAD, lrCertificateSAD, lrCertificateUDenominator,
    lrCertificateUDenominatorDeriv] using h

theorem evaluateAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluateAD terms box).Contains (lrCertificateUTarget point)
      (lrCertificateUTargetDerivS point)
      (lrCertificateUTargetDerivK point)
      (lrCertificateUTargetDerivChi point) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) < (denominatorAD box).value.lower := by
    simpa [check] using hcheck
  have h := IntervalAD.contains_divPositive hparts.2.2.2.2
    (certificate.numeratorAD_sound terms hpoint hcheck)
    (denominatorAD_sound hpoint)
  unfold evaluateAD lrCertificateUTarget lrCertificateUTargetDerivS
    lrCertificateUTargetDerivK lrCertificateUTargetDerivChi
    lrCertificateUTargetDeriv
  convert h using 1

theorem evaluate_value_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluate terms box).value.Contains
      (lrCertificateUTarget point) := by
  exact (certificate.evaluateAD_sound terms hpoint hcheck).1

end LRHighShapeMidpointCertificate

theorem lrCertificateHalfMidpointNumerator_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateHalfMidpointNumerator point =
      lrFlowNumeratorP (lrCertificateR point)
        (lrFlowM (lrCertificateV point) / 2)
        (lrCertificateV point) (lrCertificateT point) := by
  have hab := lrCertificateA_B_D_eq_flow hs he hchi
  have hg := lrCertificateGShape_eq_lrGShape he hchi
  have hw := lrCertificateW_eq_lrWKernel hs
  have hpw := lrCertificatePW_eq_lrFlowPW hs he hchi
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point ≤ 1 * lrCertificateE point :=
          mul_le_mul_of_nonneg_right hchi.2 he.1.le
        _ = lrCertificateE point := one_mul _
        _ < 1 := he.2
    linarith
  have htSq : lrCertificateT point ^ 2 = lrCertificateX point :=
    Real.sq_sqrt hxPos.le
  unfold lrCertificateHalfMidpointNumerator
    lrCertificateHalfMidpointBracket lrCertificateM lrFlowNumeratorP lrFlowM
  rw [hab.1, hab.2.1, hab.2.2, hg, hw, hpw, ← htSq]

theorem lrCertificateUTarget_eq_highShapeTarget
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateUTarget point = lrHighShapeUCertificateTarget point := by
  unfold lrCertificateUTarget lrCertificateUDenominator
    lrHighShapeUCertificateTarget
  rw [lrCertificateHalfMidpointNumerator_eq_flow hs he hchi]

end CourtadeKumar
