import InformationTheory.CourtadeKumar.LRHighShapeCoordinateAD
import InformationTheory.CourtadeKumar.LRCertificateOmega

/-!
# High-shape assembly of `W` and `P_W`

This is the common transcendental kernel of the midpoint and tangent
certificate targets.  It combines checked coordinate square roots with three
checked `omega` nodes and proves agreement with `lrWKernel` and `lrFlowPW`.
-/

open Set

namespace CourtadeKumar

def lrCertificateY0 (point : CertificatePoint) : ℝ :=
  point.chi * lrCertificateE point

noncomputable def lrCertificateW (point : CertificatePoint) : ℝ :=
  lrCertificateOmega point.s 0

noncomputable def lrCertificatePW (point : CertificatePoint) : ℝ :=
  lrCertificateOmega point.s (lrCertificateY0 point) +
    lrCertificateOmega point.s (lrCertificateE point) /
      lrCertificateV point

def lrCertificateY0DerivS (point : CertificatePoint) : ℝ :=
  point.chi * point.k

def lrCertificateY0DerivK (point : CertificatePoint) : ℝ :=
  point.chi * point.s

def lrCertificateY0DerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateE point

noncomputable def lrCertificateWDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateOmegaDeriv point.s 0 1 0

noncomputable def lrCertificateWDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateOmegaDeriv point.s 0 0 0

noncomputable def lrCertificateWDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateOmegaDeriv point.s 0 0 0

noncomputable def lrCertificatePWDeriv
    (point : CertificatePoint) (s' y0' e' v' : ℝ) : ℝ :=
  lrCertificateOmegaDeriv point.s (lrCertificateY0 point) s' y0' +
    (lrCertificateOmegaDeriv point.s (lrCertificateE point) s' e' *
        lrCertificateV point -
      lrCertificateOmega point.s (lrCertificateE point) * v') /
      lrCertificateV point ^ 2

noncomputable def lrCertificatePWDerivS (point : CertificatePoint) : ℝ :=
  lrCertificatePWDeriv point 1 (lrCertificateY0DerivS point)
    (lrCertificateEDerivS point) (lrCertificateVDerivS point)

noncomputable def lrCertificatePWDerivK (point : CertificatePoint) : ℝ :=
  lrCertificatePWDeriv point 0 (lrCertificateY0DerivK point)
    (lrCertificateEDerivK point) (lrCertificateVDerivK point)

noncomputable def lrCertificatePWDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificatePWDeriv point 0 (lrCertificateY0DerivChi point)
    (lrCertificateEDerivChi point) (lrCertificateVDerivChi point)

def lrCertificateY0AD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul (lrCertificateChiAD box) (lrCertificateEAD box)

/-- Payload for the common high-shape noise kernel. -/
structure LRHighShapeKernelCertificate where
  coordinate : LRHighShapeCoordinateCertificate
  omegaZero : LROmegaADCertificate
  omegaY0 : LROmegaADCertificate
  omegaE : LROmegaADCertificate

namespace LRHighShapeKernelCertificate

def wAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeKernelCertificate) : IntervalAD :=
  certificate.omegaZero.evaluate terms (lrCertificateSAD box)
    (IntervalAD.const 0)

def pwAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeKernelCertificate) : IntervalAD :=
  let omegaY0 := certificate.omegaY0.evaluate terms
    (lrCertificateSAD box) (lrCertificateY0AD box)
  let omegaE := certificate.omegaE.evaluate terms
    (lrCertificateSAD box) (lrCertificateEAD box)
  IntervalAD.add omegaY0
    (IntervalAD.divPositive omegaE (certificate.coordinate.vAD box))

def check (box : CertificateBox)
    (certificate : LRHighShapeKernelCertificate) : Bool :=
  decide (
    certificate.coordinate.check box = true ∧
    certificate.omegaZero.check (lrCertificateSAD box) (IntervalAD.const 0) = true ∧
    certificate.omegaY0.check (lrCertificateSAD box) (lrCertificateY0AD box) = true ∧
    certificate.omegaE.check (lrCertificateSAD box) (lrCertificateEAD box) = true ∧
    (0 : ℚ) < (certificate.coordinate.vAD box).value.lower)

end LRHighShapeKernelCertificate

theorem lrCertificateY0AD_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrCertificateY0AD box).Contains (lrCertificateY0 point)
      (lrCertificateY0DerivS point) (lrCertificateY0DerivK point)
      (lrCertificateY0DerivChi point) := by
  have hchi := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains point.chi from
      ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)
  have h := IntervalAD.contains_mul hchi (lrCertificateEAD_sound hpoint)
  simp only [lrCertificateEDerivS, lrCertificateEDerivK,
    lrCertificateEDerivChi, mul_zero, add_zero] at h
  unfold lrCertificateY0AD lrCertificateChiAD lrCertificateY0
    lrCertificateY0DerivS lrCertificateY0DerivK lrCertificateY0DerivChi
  convert h using 1 <;> ring

theorem LRHighShapeKernelCertificate.wAD_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeKernelCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.wAD terms box).Contains (lrCertificateW point)
      (lrCertificateWDerivS point) (lrCertificateWDerivK point)
      (lrCertificateWDerivChi point) := by
  have hparts :
      certificate.coordinate.check box = true ∧
      certificate.omegaZero.check (lrCertificateSAD box) (IntervalAD.const 0) = true ∧
      certificate.omegaY0.check (lrCertificateSAD box) (lrCertificateY0AD box) = true ∧
      certificate.omegaE.check (lrCertificateSAD box) (lrCertificateEAD box) = true ∧
      (0 : ℚ) < (certificate.coordinate.vAD box).value.lower := by
    simpa [LRHighShapeKernelCertificate.check] using hcheck
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have h := certificate.omegaZero.sound terms hparts.2.1 hs
    (IntervalAD.contains_const 0)
  simpa [LRHighShapeKernelCertificate.wAD, lrCertificateW,
    lrCertificateWDerivS, lrCertificateWDerivK,
    lrCertificateWDerivChi] using h

theorem LRHighShapeKernelCertificate.pwAD_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeKernelCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.pwAD terms box).Contains (lrCertificatePW point)
      (lrCertificatePWDerivS point) (lrCertificatePWDerivK point)
      (lrCertificatePWDerivChi point) := by
  have hparts :
      certificate.coordinate.check box = true ∧
      certificate.omegaZero.check (lrCertificateSAD box) (IntervalAD.const 0) = true ∧
      certificate.omegaY0.check (lrCertificateSAD box) (lrCertificateY0AD box) = true ∧
      certificate.omegaE.check (lrCertificateSAD box) (lrCertificateEAD box) = true ∧
      (0 : ℚ) < (certificate.coordinate.vAD box).value.lower := by
    simpa [LRHighShapeKernelCertificate.check] using hcheck
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hy0 := lrCertificateY0AD_sound hpoint
  have he := lrCertificateEAD_sound hpoint
  have hv := certificate.coordinate.vAD_sound hpoint hparts.1
  have homegaY0 := certificate.omegaY0.sound terms hparts.2.2.1 hs hy0
  have homegaE := certificate.omegaE.sound terms hparts.2.2.2.1 hs he
  have hquot := IntervalAD.contains_divPositive hparts.2.2.2.2
    homegaE hv
  have h := IntervalAD.contains_add homegaY0 hquot
  unfold LRHighShapeKernelCertificate.pwAD lrCertificatePW
    lrCertificatePWDerivS lrCertificatePWDerivK lrCertificatePWDerivChi
    lrCertificatePWDeriv
  dsimp only
  convert h using 1

lemma lrCertificateW_eq_lrWKernel
    {point : CertificatePoint} (hs : point.s ∈ Ioo (0 : ℝ) 1) :
    lrCertificateW point = lrWKernel (lrCertificateR point) 1 := by
  have h := lrCertificateOmega_one_sub_sq hs
    (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)
  simpa [lrCertificateW, lrCertificateR] using h

theorem lrCertificatePW_eq_lrFlowPW
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificatePW point =
      lrFlowPW (lrCertificateR point) (lrCertificateV point)
        (lrCertificateT point) := by
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point ≤ 1 * lrCertificateE point := by
          exact mul_le_mul_of_nonneg_right hchi.2 he.1.le
        _ = lrCertificateE point := one_mul _
        _ < 1 := he.2
    linarith
  have hxLe : lrCertificateX point ≤ 1 := by
    unfold lrCertificateX
    exact sub_le_self _ (mul_nonneg hchi.1 he.1.le)
  have htSq : lrCertificateT point ^ 2 = lrCertificateX point := by
    exact Real.sq_sqrt hxPos.le
  have htMem : lrCertificateT point ∈ Ioc (0 : ℝ) 1 := by
    have htPos : 0 < lrCertificateT point := Real.sqrt_pos.2 hxPos
    exact ⟨htPos, by nlinarith [htSq]⟩
  have hnumLe : 1 - lrCertificateE point ≤ lrCertificateX point := by
    unfold lrCertificateX
    have := mul_le_mul_of_nonneg_right hchi.2 he.1.le
    nlinarith
  have hradPos : 0 < (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hradLe : (1 - lrCertificateE point) / lrCertificateX point ≤ 1 := by
    rw [div_le_one hxPos]
    exact hnumLe
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point := by
    exact Real.sq_sqrt hradPos.le
  have hvMem : lrCertificateV point ∈ Ioc (0 : ℝ) 1 := by
    have hvPos : 0 < lrCertificateV point := Real.sqrt_pos.2 hradPos
    exact ⟨hvPos, by nlinarith [hvSq, hradLe]⟩
  have hvtSq : (lrCertificateV point * lrCertificateT point) ^ 2 =
      1 - lrCertificateE point := by
    rw [mul_pow, hvSq, htSq]
    field_simp [hxPos.ne']
  have hvtMem : lrCertificateV point * lrCertificateT point ∈
      Ioc (0 : ℝ) 1 := by
    have hvtPos := mul_pos hvMem.1 htMem.1
    exact ⟨hvtPos, by nlinarith [hvtSq, he.1]⟩
  have hy0 : lrCertificateY0 point =
      1 - lrCertificateT point ^ 2 := by
    unfold lrCertificateY0
    rw [htSq]
    unfold lrCertificateX
    ring
  have heq : lrCertificateE point =
      1 - (lrCertificateV point * lrCertificateT point) ^ 2 := by
    linarith [hvtSq]
  have homegaY0 := lrCertificateOmega_one_sub_sq hs htMem
  have homegaE := lrCertificateOmega_one_sub_sq hs hvtMem
  rw [← hy0] at homegaY0
  rw [← heq] at homegaE
  unfold lrCertificatePW lrFlowPW lrCertificateR
  rw [homegaY0, homegaE]

end CourtadeKumar
