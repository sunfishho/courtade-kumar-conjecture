import InformationTheory.CourtadeKumar.LRHighShapeCertificateCoordinates
import InformationTheory.CourtadeKumar.IntervalADElementary
import InformationTheory.CourtadeKumar.IntervalMidpointCertificate

/-!
# Verified interval AD for the high-shape coordinate map

This module evaluates `e`, `x`, `R`, `t`, and `v` from a rational
`(s,k,χ)` box.  Square-root data are untrusted payloads; the Boolean checker
verifies them before the semantic theorems expose values and all three
coordinate derivatives.
-/

open Set

namespace CourtadeKumar

def lrCertificateEDerivS (point : CertificatePoint) : ℝ := point.k
def lrCertificateEDerivK (point : CertificatePoint) : ℝ := point.s
def lrCertificateEDerivChi (_point : CertificatePoint) : ℝ := 0

def lrCertificateXDerivS (point : CertificatePoint) : ℝ :=
  -point.chi * point.k

def lrCertificateXDerivK (point : CertificatePoint) : ℝ :=
  -point.chi * point.s

def lrCertificateXDerivChi (point : CertificatePoint) : ℝ :=
  -lrCertificateE point

def lrCertificateRDerivS (_point : CertificatePoint) : ℝ := -1
def lrCertificateRDerivK (_point : CertificatePoint) : ℝ := 0
def lrCertificateRDerivChi (_point : CertificatePoint) : ℝ := 0

noncomputable def lrCertificateTDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateXDerivS point / (2 * lrCertificateT point)

noncomputable def lrCertificateTDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateXDerivK point / (2 * lrCertificateT point)

noncomputable def lrCertificateTDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateXDerivChi point / (2 * lrCertificateT point)

noncomputable def lrCertificateVRadicand (point : CertificatePoint) : ℝ :=
  (1 - lrCertificateE point) / lrCertificateX point

noncomputable def lrCertificateVRadicandDeriv
    (point : CertificatePoint) (e' x' : ℝ) : ℝ :=
  ((-e') * lrCertificateX point -
      (1 - lrCertificateE point) * x') /
    lrCertificateX point ^ 2

noncomputable def lrCertificateVDeriv
    (point : CertificatePoint) (e' x' : ℝ) : ℝ :=
  lrCertificateVRadicandDeriv point e' x' /
    (2 * lrCertificateV point)

noncomputable def lrCertificateVRadicandDerivS
    (point : CertificatePoint) : ℝ :=
  ((-lrCertificateEDerivS point) * lrCertificateX point -
      (1 - lrCertificateE point) * lrCertificateXDerivS point) /
    lrCertificateX point ^ 2

noncomputable def lrCertificateVRadicandDerivK
    (point : CertificatePoint) : ℝ :=
  ((-lrCertificateEDerivK point) * lrCertificateX point -
      (1 - lrCertificateE point) * lrCertificateXDerivK point) /
    lrCertificateX point ^ 2

noncomputable def lrCertificateVRadicandDerivChi
    (point : CertificatePoint) : ℝ :=
  ((-lrCertificateEDerivChi point) * lrCertificateX point -
      (1 - lrCertificateE point) * lrCertificateXDerivChi point) /
    lrCertificateX point ^ 2

noncomputable def lrCertificateVDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateVRadicandDerivS point / (2 * lrCertificateV point)

noncomputable def lrCertificateVDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateVRadicandDerivK point / (2 * lrCertificateV point)

noncomputable def lrCertificateVDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateVRadicandDerivChi point / (2 * lrCertificateV point)

/-- A generic three-coordinate curve, used to prove the analytic chain rule
once before specializing to the `s`, `k`, and `chi` coordinate lines. -/
def lrCertificateCurve (s k chi : ℝ → ℝ) (q : ℝ) : CertificatePoint where
  s := s q
  k := k q
  chi := chi q

theorem hasDerivAt_lrCertificateE_curve
    {z s' k' : ℝ} {s k chi : ℝ → ℝ}
    (hs : HasDerivAt s s' z) (hk : HasDerivAt k k' z) :
    HasDerivAt (fun q ↦ lrCertificateE (lrCertificateCurve s k chi q))
      (s' * k z + s z * k') z := by
  simpa [lrCertificateE, lrCertificateCurve] using hs.mul hk

theorem hasDerivAt_lrCertificateX_curve
    {z s' k' chi' : ℝ} {s k chi : ℝ → ℝ}
    (hs : HasDerivAt s s' z) (hk : HasDerivAt k k' z)
    (hchi : HasDerivAt chi chi' z) :
    HasDerivAt (fun q ↦ lrCertificateX (lrCertificateCurve s k chi q))
      (-(chi' * lrCertificateE (lrCertificateCurve s k chi z) +
        chi z * (s' * k z + s z * k'))) z := by
  have he := hasDerivAt_lrCertificateE_curve (chi := chi) hs hk
  have hprod := hchi.mul he
  have h := (hasDerivAt_const z 1).sub hprod
  unfold lrCertificateX
  convert h using 1 <;> ring

theorem hasDerivAt_lrCertificateV_curve
    {z s' k' chi' : ℝ} {s k chi : ℝ → ℝ}
    (hs : HasDerivAt s s' z) (hk : HasDerivAt k k' z)
    (hchi : HasDerivAt chi chi' z)
    (heMem : lrCertificateE (lrCertificateCurve s k chi z) ∈ Ioo (0 : ℝ) 1)
    (hchiMem : chi z ∈ Ioo (0 : ℝ) 1) :
    let point := lrCertificateCurve s k chi z
    let e' := s' * k z + s z * k'
    let x' := -(chi' * lrCertificateE point + chi z * e')
    HasDerivAt (fun q ↦ lrCertificateV (lrCertificateCurve s k chi q))
      (lrCertificateVDeriv point e' x') z := by
  dsimp only
  let point := lrCertificateCurve s k chi z
  let e' := s' * k z + s z * k'
  let x' := -(chi' * lrCertificateE point + chi z * e')
  have he := hasDerivAt_lrCertificateE_curve (chi := chi) hs hk
  have hx := hasDerivAt_lrCertificateX_curve hs hk hchi
  have hxPos : 0 < lrCertificateX point := by
    change 0 < 1 - chi z *
      lrCertificateE (lrCertificateCurve s k chi z)
    have hprod : chi z * lrCertificateE (lrCertificateCurve s k chi z) < 1 := by
      calc
        chi z * lrCertificateE (lrCertificateCurve s k chi z) <
            1 * lrCertificateE (lrCertificateCurve s k chi z) :=
          mul_lt_mul_of_pos_right hchiMem.2 heMem.1
        _ = lrCertificateE (lrCertificateCurve s k chi z) := one_mul _
        _ < 1 := heMem.2
    exact sub_pos.mpr hprod
  have hnum := (hasDerivAt_const z 1).sub he
  have hradRaw := hnum.div hx hxPos.ne'
  have hrad : HasDerivAt
      (fun q ↦ lrCertificateVRadicand (lrCertificateCurve s k chi q))
      (lrCertificateVRadicandDeriv point e' x') z := by
    unfold lrCertificateVRadicand lrCertificateVRadicandDeriv
    convert hradRaw using 1 <;>
      simp only [Pi.sub_apply] <;>
      dsimp [point, e', x', lrCertificateCurve, lrCertificateE,
        lrCertificateX] <;> ring
  have hradPos : 0 < lrCertificateVRadicand point :=
    div_pos (sub_pos.mpr heMem.2) hxPos
  have hsqrt := (Real.hasDerivAt_sqrt hradPos.ne').comp z hrad
  have hsqrtEq : Real.sqrt (lrCertificateVRadicand point) =
      lrCertificateV point := by rfl
  unfold lrCertificateV lrCertificateVDeriv
  convert hsqrt using 1
  rw [hsqrtEq]
  dsimp [point, e', x']
  field_simp

def lrCertificateSAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableS box.sInterval

def lrCertificateKAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableK box.kInterval

def lrCertificateChiAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableChi box.chiInterval

def lrCertificateEAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul (lrCertificateSAD box) (lrCertificateKAD box)

def lrCertificateXAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.sub (IntervalAD.const 1)
    (IntervalAD.mul (lrCertificateChiAD box) (lrCertificateEAD box))

def lrCertificateRAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.sub (IntervalAD.const 1) (lrCertificateSAD box)

def lrCertificateVRadicandAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.const 1) (lrCertificateEAD box))
    (lrCertificateXAD box)

/-- The only untrusted data in the coordinate map are the two square-root
enclosures. -/
structure LRHighShapeCoordinateCertificate where
  tSqrt : RationalEnclosure.SqrtCertificate
  vSqrt : RationalEnclosure.SqrtCertificate

namespace LRHighShapeCoordinateCertificate

def tAD (box : CertificateBox)
    (certificate : LRHighShapeCoordinateCertificate) : IntervalAD :=
  IntervalAD.sqrt certificate.tSqrt (lrCertificateXAD box)

def vAD (box : CertificateBox)
    (certificate : LRHighShapeCoordinateCertificate) : IntervalAD :=
  IntervalAD.sqrt certificate.vSqrt (lrCertificateVRadicandAD box)

def check (box : CertificateBox)
    (certificate : LRHighShapeCoordinateCertificate) : Bool :=
  IntervalAD.sqrtCheck (lrCertificateXAD box).value certificate.tSqrt &&
    decide ((0 : ℚ) < (lrCertificateXAD box).value.lower) &&
    IntervalAD.sqrtCheck (lrCertificateVRadicandAD box).value certificate.vSqrt

end LRHighShapeCoordinateCertificate

theorem lrCertificateEAD_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrCertificateEAD box).Contains (lrCertificateE point)
      (lrCertificateEDerivS point) (lrCertificateEDerivK point)
      (lrCertificateEDerivChi point) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hk := IntervalAD.contains_variableK
    (show box.kInterval.Contains point.k from
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  simpa [lrCertificateEAD, lrCertificateSAD, lrCertificateKAD,
    lrCertificateE, lrCertificateEDerivS, lrCertificateEDerivK,
    lrCertificateEDerivChi] using IntervalAD.contains_mul hs hk

theorem lrCertificateXAD_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrCertificateXAD box).Contains (lrCertificateX point)
      (lrCertificateXDerivS point) (lrCertificateXDerivK point)
      (lrCertificateXDerivChi point) := by
  have hchi := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains point.chi from
      ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)
  have hprod := IntervalAD.contains_mul hchi (lrCertificateEAD_sound hpoint)
  have h := IntervalAD.contains_sub (IntervalAD.contains_const 1) hprod
  simp only [lrCertificateEDerivS, lrCertificateEDerivK,
    lrCertificateEDerivChi, mul_zero, add_zero] at h
  unfold lrCertificateXAD lrCertificateX lrCertificateXDerivS
    lrCertificateXDerivK lrCertificateXDerivChi lrCertificateChiAD
  convert h using 1 <;> ring

theorem lrCertificateRAD_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lrCertificateRAD box).Contains (lrCertificateR point)
      (lrCertificateRDerivS point) (lrCertificateRDerivK point)
      (lrCertificateRDerivChi point) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have h := IntervalAD.contains_sub (IntervalAD.contains_const 1) hs
  simpa [lrCertificateRAD, lrCertificateSAD, lrCertificateR,
    lrCertificateRDerivS, lrCertificateRDerivK,
    lrCertificateRDerivChi] using h

theorem lrCertificateVRadicandAD_sound {box : CertificateBox}
    {point : CertificatePoint} (hpoint : box.Contains point)
    (hxLower : (0 : ℚ) < (lrCertificateXAD box).value.lower) :
    (lrCertificateVRadicandAD box).Contains (lrCertificateVRadicand point)
      (lrCertificateVRadicandDerivS point)
      (lrCertificateVRadicandDerivK point)
      (lrCertificateVRadicandDerivChi point) := by
  have hnum := IntervalAD.contains_sub (IntervalAD.contains_const 1)
    (lrCertificateEAD_sound hpoint)
  have h := IntervalAD.contains_divPositive hxLower hnum
    (lrCertificateXAD_sound hpoint)
  unfold lrCertificateVRadicandAD lrCertificateVRadicand
    lrCertificateVRadicandDerivS lrCertificateVRadicandDerivK
    lrCertificateVRadicandDerivChi
  convert h using 1
  all_goals norm_num

theorem LRHighShapeCoordinateCertificate.tAD_sound
    {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeCoordinateCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.check box = true) :
    (certificate.tAD box).Contains (lrCertificateT point)
      (lrCertificateTDerivS point) (lrCertificateTDerivK point)
      (lrCertificateTDerivChi point) := by
  have hparts :
      (IntervalAD.sqrtCheck (lrCertificateXAD box).value certificate.tSqrt = true ∧
        (0 : ℚ) < (lrCertificateXAD box).value.lower) ∧
      IntervalAD.sqrtCheck (lrCertificateVRadicandAD box).value
        certificate.vSqrt = true := by
    simpa [LRHighShapeCoordinateCertificate.check] using hcheck
  have h := IntervalAD.contains_sqrt hparts.1.1
    (lrCertificateXAD_sound hpoint)
  simpa [LRHighShapeCoordinateCertificate.tAD, lrCertificateT,
    lrCertificateTDerivS, lrCertificateTDerivK,
    lrCertificateTDerivChi] using h

theorem LRHighShapeCoordinateCertificate.vAD_sound
    {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeCoordinateCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.check box = true) :
    (certificate.vAD box).Contains (lrCertificateV point)
      (lrCertificateVDerivS point) (lrCertificateVDerivK point)
      (lrCertificateVDerivChi point) := by
  have hparts :
      (IntervalAD.sqrtCheck (lrCertificateXAD box).value certificate.tSqrt = true ∧
        (0 : ℚ) < (lrCertificateXAD box).value.lower) ∧
      IntervalAD.sqrtCheck (lrCertificateVRadicandAD box).value
        certificate.vSqrt = true := by
    simpa [LRHighShapeCoordinateCertificate.check] using hcheck
  have hrad := lrCertificateVRadicandAD_sound hpoint hparts.1.2
  have h := IntervalAD.contains_sqrt hparts.2 hrad
  simpa [LRHighShapeCoordinateCertificate.vAD, lrCertificateV,
    lrCertificateVRadicand, lrCertificateVDerivS, lrCertificateVDerivK,
    lrCertificateVDerivChi] using h

end CourtadeKumar
