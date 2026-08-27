import InformationTheory.CourtadeKumar.LRHighShapeGAssembly

/-!
# Cancellation-safe assembly of `A`, `B`, and `D`

The exact replay evaluates the logarithmic coefficients through `e` and
`b_s(e)`, avoiding subtraction near the singular radial endpoint.
-/

open Set

namespace CourtadeKumar

noncomputable def lrCertificateA (point : CertificatePoint) : ℝ :=
  Real.log (1 + lrCertificateV point) -
    (1 / 2 : ℝ) * Real.log (lrCertificateE point)

noncomputable def lrCertificateBFlow (point : CertificatePoint) : ℝ :=
  Real.log (1 + lrCertificateV point) -
    (1 / 2 : ℝ) * Real.log (lrCertificateB point.s (lrCertificateE point))

noncomputable def lrCertificateD (point : CertificatePoint) : ℝ :=
  lrCertificateA point - lrCertificateBFlow point

noncomputable def lrCertificateADeriv
    (point : CertificatePoint) (e' v' : ℝ) : ℝ :=
  v' / (1 + lrCertificateV point) -
    (1 / 2 : ℝ) * (e' / lrCertificateE point)

noncomputable def lrCertificateBFlowDeriv
    (point : CertificatePoint) (s' e' v' : ℝ) : ℝ :=
  v' / (1 + lrCertificateV point) -
    (1 / 2 : ℝ) *
      (lrCertificateBDeriv point.s (lrCertificateE point) s' e' /
        lrCertificateB point.s (lrCertificateE point))

noncomputable def lrCertificateDDeriv
    (point : CertificatePoint) (s' e' v' : ℝ) : ℝ :=
  lrCertificateADeriv point e' v' -
    lrCertificateBFlowDeriv point s' e' v'

structure LRHighShapeABAD where
  a : IntervalAD
  b : IntervalAD
  d : IntervalAD

/-- Three logarithm range-reduction payloads for `A`, `B`, and `D`. -/
structure LRHighShapeABCertificate where
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logE : RationalEnclosure.LogIntervalCertificate
  logBE : RationalEnclosure.LogIntervalCertificate

namespace LRHighShapeABCertificate

def evaluate (terms : ℕ) (box : CertificateBox)
    (coordinate : LRHighShapeCoordinateCertificate)
    (certificate : LRHighShapeABCertificate) : LRHighShapeABAD :=
  let v := coordinate.vAD box
  let e := lrCertificateEAD box
  let be := lrCertificateBAD (lrCertificateSAD box) e
  let logOnePlus := IntervalAD.log terms certificate.logOnePlusV
    (IntervalAD.add (IntervalAD.const 1) v)
  let logE := IntervalAD.log terms certificate.logE e
  let logBE := IntervalAD.log terms certificate.logBE be
  let a := IntervalAD.sub logOnePlus
    (IntervalAD.mul (IntervalAD.const (1 / 2)) logE)
  let b := IntervalAD.sub logOnePlus
    (IntervalAD.mul (IntervalAD.const (1 / 2)) logBE)
  { a := a, b := b, d := IntervalAD.sub a b }

def check (box : CertificateBox)
    (coordinate : LRHighShapeCoordinateCertificate)
    (certificate : LRHighShapeABCertificate) : Bool :=
  let v := coordinate.vAD box
  let e := lrCertificateEAD box
  let be := lrCertificateBAD (lrCertificateSAD box) e
  decide (
    coordinate.check box = true ∧
    certificate.logOnePlusV.check
      (IntervalAD.add (IntervalAD.const 1) v).value = true ∧
    certificate.logE.check e.value = true ∧
    certificate.logBE.check be.value = true)

theorem sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {coordinate : LRHighShapeCoordinateCertificate}
    {certificate : LRHighShapeABCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.check box coordinate = true) :
    let result := certificate.evaluate terms box coordinate
    result.a.Contains (lrCertificateA point)
      (lrCertificateADeriv point (lrCertificateEDerivS point)
        (lrCertificateVDerivS point))
      (lrCertificateADeriv point (lrCertificateEDerivK point)
        (lrCertificateVDerivK point))
      (lrCertificateADeriv point (lrCertificateEDerivChi point)
        (lrCertificateVDerivChi point)) ∧
    result.b.Contains (lrCertificateBFlow point)
      (lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
        (lrCertificateVDerivS point))
      (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
        (lrCertificateVDerivK point))
      (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
        (lrCertificateVDerivChi point)) ∧
    result.d.Contains (lrCertificateD point)
      (lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
        (lrCertificateVDerivS point))
      (lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
        (lrCertificateVDerivK point))
      (lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
        (lrCertificateVDerivChi point)) := by
  dsimp only
  let v := coordinate.vAD box
  let e := lrCertificateEAD box
  let be := lrCertificateBAD (lrCertificateSAD box) e
  have hparts :
      coordinate.check box = true ∧
      certificate.logOnePlusV.check
        (IntervalAD.add (IntervalAD.const 1) v).value = true ∧
      certificate.logE.check e.value = true ∧
      certificate.logBE.check be.value = true := by
    simpa [check, v, e, be] using hcheck
  have hv := coordinate.vAD_sound hpoint hparts.1
  have he := lrCertificateEAD_sound hpoint
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hbe := lrCertificateBAD_sound hs he
  have honePlus := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have hlogOnePlus := IntervalAD.contains_log terms hparts.2.1 honePlus
  have hlogE := IntervalAD.contains_log terms hparts.2.2.1 he
  have hlogBE := IntervalAD.contains_log terms hparts.2.2.2 hbe
  have hhalf := IntervalAD.contains_const (1 / 2 : ℚ)
  have ha := IntervalAD.contains_sub hlogOnePlus
    (IntervalAD.contains_mul hhalf hlogE)
  have hb := IntervalAD.contains_sub hlogOnePlus
    (IntervalAD.contains_mul hhalf hlogBE)
  have hd := IntervalAD.contains_sub ha hb
  unfold evaluate
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa [lrCertificateA, lrCertificateADeriv] using ha
  · simpa [lrCertificateBFlow, lrCertificateBFlowDeriv] using hb
  · simpa [lrCertificateD, lrCertificateDDeriv, lrCertificateA,
      lrCertificateBFlow, lrCertificateADeriv, lrCertificateBFlowDeriv] using hd

end LRHighShapeABCertificate

theorem lrCertificateA_B_D_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateA point =
        lrFlowA (lrCertificateV point) (lrCertificateT point) ∧
    lrCertificateBFlow point =
        lrFlowB (lrCertificateR point) (lrCertificateV point)
          (lrCertificateT point) ∧
    lrCertificateD point =
        lrFlowD (lrCertificateR point) (lrCertificateV point)
          (lrCertificateT point) := by
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
  have hradPos : 0 < (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point :=
    Real.sq_sqrt hradPos.le
  have hvtSq : (lrCertificateV point * lrCertificateT point) ^ 2 =
      1 - lrCertificateE point := by
    rw [mul_pow, hvSq, htSq]
    field_simp [hxPos.ne']
  have hRnonneg : 0 ≤ lrCertificateR point := by
    unfold lrCertificateR
    linarith [hs.2]
  have hsqrtRSq : Real.sqrt (lrCertificateR point) ^ 2 =
      lrCertificateR point := Real.sq_sqrt hRnonneg
  have hrhovtSq :
      (Real.sqrt (lrCertificateR point) * lrCertificateV point *
        lrCertificateT point) ^ 2 =
      1 - lrCertificateB point.s (lrCertificateE point) := by
    rw [show (Real.sqrt (lrCertificateR point) * lrCertificateV point *
        lrCertificateT point) ^ 2 =
      Real.sqrt (lrCertificateR point) ^ 2 *
        (lrCertificateV point * lrCertificateT point) ^ 2 by ring,
      hsqrtRSq, hvtSq]
    unfold lrCertificateR lrCertificateB
    ring
  have hA : lrCertificateA point =
      lrFlowA (lrCertificateV point) (lrCertificateT point) := by
    unfold lrCertificateA lrFlowA lrFlowBeta lrL
    rw [show 1 - (lrCertificateV point * lrCertificateT point) ^ 2 =
        lrCertificateE point by linarith [hvtSq]]
    ring
  have hB : lrCertificateBFlow point =
      lrFlowB (lrCertificateR point) (lrCertificateV point)
        (lrCertificateT point) := by
    unfold lrCertificateBFlow lrFlowB lrFlowBeta lrL
    rw [show 1 - (Real.sqrt (lrCertificateR point) *
        lrCertificateV point * lrCertificateT point) ^ 2 =
      lrCertificateB point.s (lrCertificateE point) by
        linarith [hrhovtSq]]
    ring
  refine ⟨hA, hB, ?_⟩
  unfold lrCertificateD lrFlowD
  rw [hA, hB]

end CourtadeKumar
