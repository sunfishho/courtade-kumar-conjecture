import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore
import InformationTheory.CourtadeKumar.LRHighShapeKernelAssembly
import InformationTheory.CourtadeKumar.LRCertificateG0

/-!
# Cancellation-safe assembly of `G_t`

This module verifies the interval-AD expression
`g₀(v) + Q(χe) + Q(e)/v` and proves that it is exactly the existing
`lrGShape t v` in physical high-shape coordinates.
-/

open Set

namespace CourtadeKumar


noncomputable def lrCertificateGShapeValueDeriv
    (y0 e v y0' e' v' : ℝ) : ℝ :=
  lrCertificateG0Prime v * v' + lrCertificateQPrime y0 * y0' +
    (lrCertificateQPrime e * e' * v - lrCertificateQ e * v') / v ^ 2


noncomputable def lrCertificateGShapeDeriv
    (point : CertificatePoint) (y0' e' v' : ℝ) : ℝ :=
  lrCertificateGShapeValueDeriv (lrCertificateY0 point)
    (lrCertificateE point) (lrCertificateV point) y0' e' v'

theorem hasDerivAt_lrCertificateGShapeValue_along
    {z y0' e' v' : ℝ} {y0fun efun vfun : ℝ → ℝ}
    (hy0 : HasDerivAt y0fun y0' z) (he : HasDerivAt efun e' z)
    (hv : HasDerivAt vfun v' z)
    (hy0Mem : y0fun z ∈ Ioo (0 : ℝ) 1)
    (heMem : efun z ∈ Ioo (0 : ℝ) 1)
    (hvPos : 0 < vfun z) :
    HasDerivAt
      (fun q ↦ lrCertificateGShapeValue (y0fun q) (efun q) (vfun q))
      (lrCertificateGShapeValueDeriv (y0fun z) (efun z) (vfun z)
        y0' e' v') z := by
  have hg0 := (hasDerivAt_lrCertificateG0 hvPos).comp z hv
  have hqY0 := (hasDerivAt_lrCertificateQ hy0Mem).comp z hy0
  have hqE := (hasDerivAt_lrCertificateQ heMem).comp z he
  have hquot := hqE.div hv hvPos.ne'
  have h := (hg0.add hqY0).add hquot
  unfold lrCertificateGShapeValue lrCertificateGShapeValueDeriv
  convert h using 1 <;> field_simp [hvPos.ne'] <;> ring

noncomputable def lrCertificateGShapeDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateGShapeDeriv point (lrCertificateY0DerivS point)
    (lrCertificateEDerivS point) (lrCertificateVDerivS point)

noncomputable def lrCertificateGShapeDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateGShapeDeriv point (lrCertificateY0DerivK point)
    (lrCertificateEDerivK point) (lrCertificateVDerivK point)

noncomputable def lrCertificateGShapeDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateGShapeDeriv point (lrCertificateY0DerivChi point)
    (lrCertificateEDerivChi point) (lrCertificateVDerivChi point)

/-- Scalar payloads for `G_t`; the coordinate square-root certificate is
shared with the surrounding high-shape kernel. -/
structure LRHighShapeGCertificate where
  g0 : LRG0ADCertificate
  qY0 : LRQADCertificate
  qE : LRQADCertificate

namespace LRHighShapeGCertificate

def evaluate (terms : ℕ) (box : CertificateBox)
    (coordinate : LRHighShapeCoordinateCertificate)
    (certificate : LRHighShapeGCertificate) : IntervalAD :=
  let v := coordinate.vAD box
  let g0 := certificate.g0.evaluate terms v
  let qY0 := certificate.qY0.evaluate terms (lrCertificateY0AD box)
  let qE := certificate.qE.evaluate terms (lrCertificateEAD box)
  IntervalAD.add (IntervalAD.add g0 qY0) (IntervalAD.divPositive qE v)

def check (box : CertificateBox)
    (coordinate : LRHighShapeCoordinateCertificate)
    (certificate : LRHighShapeGCertificate) : Bool :=
  decide (
    coordinate.check box = true ∧
    certificate.g0.check (coordinate.vAD box) = true ∧
    certificate.qY0.check (lrCertificateY0AD box).value = true ∧
    certificate.qE.check (lrCertificateEAD box).value = true ∧
    (0 : ℚ) < (coordinate.vAD box).value.lower)

theorem sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {coordinate : LRHighShapeCoordinateCertificate}
    {certificate : LRHighShapeGCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.check box coordinate = true) :
    (certificate.evaluate terms box coordinate).Contains
      (lrCertificateGShape point)
      (lrCertificateGShapeDerivS point)
      (lrCertificateGShapeDerivK point)
      (lrCertificateGShapeDerivChi point) := by
  have hparts :
      coordinate.check box = true ∧
      certificate.g0.check (coordinate.vAD box) = true ∧
      certificate.qY0.check (lrCertificateY0AD box).value = true ∧
      certificate.qE.check (lrCertificateEAD box).value = true ∧
      (0 : ℚ) < (coordinate.vAD box).value.lower := by
    simpa [check] using hcheck
  have hv := coordinate.vAD_sound hpoint hparts.1
  have hy0 := lrCertificateY0AD_sound hpoint
  have he := lrCertificateEAD_sound hpoint
  have hg0 := certificate.g0.sound terms hparts.2.1 hv
  have hqY0 := certificate.qY0.sound terms hparts.2.2.1 hy0
  have hqE := certificate.qE.sound terms hparts.2.2.2.1 he
  have hquot := IntervalAD.contains_divPositive hparts.2.2.2.2 hqE hv
  have h := IntervalAD.contains_add (IntervalAD.contains_add hg0 hqY0) hquot
  unfold evaluate lrCertificateGShape lrCertificateGShapeValue
    lrCertificateGShapeDerivS
    lrCertificateGShapeDerivK lrCertificateGShapeDerivChi
    lrCertificateGShapeDeriv lrCertificateGShapeValueDeriv
  dsimp only
  convert h using 1

end LRHighShapeGCertificate

theorem lrCertificateGShape_eq_lrGShape
    {point : CertificatePoint}
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateGShape point =
      lrGShape (lrCertificateT point) (lrCertificateV point) := by
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
  have htPos : 0 < lrCertificateT point := Real.sqrt_pos.2 hxPos
  have hnumPos : 0 < 1 - lrCertificateE point := sub_pos.mpr he.2
  have hradPos : 0 < (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos hnumPos hxPos
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point :=
    Real.sq_sqrt hradPos.le
  have hvPos : 0 < lrCertificateV point := Real.sqrt_pos.2 hradPos
  have hvtSq : (lrCertificateV point * lrCertificateT point) ^ 2 =
      1 - lrCertificateE point := by
    rw [mul_pow, hvSq, htSq]
    field_simp [hxPos.ne']
  have hy0 : lrCertificateY0 point =
      1 - lrCertificateT point ^ 2 := by
    unfold lrCertificateY0
    rw [htSq]
    unfold lrCertificateX
    ring
  have hsqrtY0 :
      Real.sqrt (1 - lrCertificateY0 point) = lrCertificateT point := by
    rw [hy0, show 1 - (1 - lrCertificateT point ^ 2) =
        lrCertificateT point ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos htPos]
  have heq : lrCertificateE point =
      1 - (lrCertificateV point * lrCertificateT point) ^ 2 := by
    linarith [hvtSq]
  have hsqrtE : Real.sqrt (1 - lrCertificateE point) =
      lrCertificateV point * lrCertificateT point := by
    rw [heq, show 1 - (1 - (lrCertificateV point *
        lrCertificateT point) ^ 2) =
          (lrCertificateV point * lrCertificateT point) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hvPos htPos)]
  unfold lrCertificateGShape lrCertificateGShapeValue
  rw [lrCertificateG0_eq_lrG, lrCertificateQ_eq, lrCertificateQ_eq,
    hsqrtY0, hsqrtE]
  unfold lrGShape
  field_simp [hvPos.ne']
  ring

end CourtadeKumar
