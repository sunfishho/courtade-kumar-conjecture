import InformationTheory.CourtadeKumar.LRHighShapeQZeroSKEvaluator

/-!
# Endpoint-safe smooth derivatives of `omega_s(χe)`

The value-only zero-face kernel already evaluates `omega_s(y)` when the
input interval for `y` touches zero.  This module strengthens that node in
the two smooth coordinates.  It uses the regularized evaluator for
`Q(χe)` and ordinary checked `Q'`, `Q''` enclosures only at
`b_s(χe) ≥ s > 0`.  Thus its value, `s` derivative, and `k` derivative are
valid across `χ = 0`; no claim is made about its synthetic `χ` derivative.
-/

namespace CourtadeKumar
namespace LROmegaZeroIntervalCertificate

/-- Endpoint-safe interval-AD expression for `omega_s(χe)`. -/
def evaluateY0SK (terms : ℕ) (box : CertificateBox)
    (certificate : LROmegaZeroIntervalCertificate) : IntervalAD :=
  let s := lrCertificateSAD box
  let y := lrCertificateY0NonnegativeAD box
  let b := lrCertificateBAD s y
  let qPrimeB := certificate.qPrimeAtB.enclosure terms
  let qB := IntervalAD.unary (certificate.qAtB.enclosure terms) qPrimeB b
  let qY := certificate.qAtY.evaluateY0SK terms box
  let qPrimeBAD := IntervalAD.unary qPrimeB
    (lrQSecondCoarseEnclosure b.value) b
  IntervalAD.sub (IntervalAD.sub qB qY)
    (IntervalAD.mul (IntervalAD.mul s
      (IntervalAD.sub (IntervalAD.const 1) y)) qPrimeBAD)

/-- Soundness of the endpoint-safe value and smooth derivative fields. -/
theorem evaluateY0SK_sound (terms : ℕ) {box : CertificateBox}
    {certificate : LROmegaZeroIntervalCertificate}
    (hcheck : certificate.check (lrCertificateSAD box)
      (lrCertificateY0NonnegativeAD box) = true)
    (hsPos : (0 : ℚ) < box.sLo) (hkPos : (0 : ℚ) < box.kLo)
    (hchi : (0 : ℚ) ≤ box.chiLo)
    (he : (0 : ℚ) ≤ (lrCertificateEAD box).value.lower)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    let result := certificate.evaluateY0SK terms box
    result.value.Contains
        (lrCertificateOmega point.s (lrCertificateY0 point)) ∧
      result.derivS.Contains
        (lrCertificateOmegaDeriv point.s (lrCertificateY0 point)
          1 (lrCertificateY0DerivS point)) ∧
      result.derivK.Contains
        (lrCertificateOmegaDeriv point.s (lrCertificateY0 point)
          0 (lrCertificateY0DerivK point)) := by
  dsimp only
  let s := lrCertificateSAD box
  let y := lrCertificateY0NonnegativeAD box
  let b := lrCertificateBAD s y
  let qPrimeB := certificate.qPrimeAtB.enclosure terms
  let qB := IntervalAD.unary (certificate.qAtB.enclosure terms) qPrimeB b
  let qY := certificate.qAtY.evaluateY0SK terms box
  let qPrimeBAD := IntervalAD.unary qPrimeB
    (lrQSecondCoarseEnclosure b.value) b
  have hparts :
      (certificate.qAtB.check b.value = true ∧
        certificate.qAtY.check y.value = true) ∧
        certificate.qPrimeAtB.check b.value = true := by
    simpa [LROmegaZeroIntervalCertificate.check, s, y, b] using hcheck
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hy := lrCertificateY0NonnegativeAD_sound hpoint hchi he
  have hb := lrCertificateBAD_sound hs hy
  have hqBValue := certificate.qAtB.sound terms hparts.1.1 hb.1
  have hqPrimeBValue := certificate.qPrimeAtB.sound terms hparts.2 hb.1
  have hqB : qB.Contains
      (lrCertificateQ (lrCertificateB point.s (lrCertificateY0 point)))
      (lrCertificateQPrime
          (lrCertificateB point.s (lrCertificateY0 point)) *
        lrCertificateBDeriv point.s (lrCertificateY0 point)
          1 (lrCertificateY0DerivS point))
      (lrCertificateQPrime
          (lrCertificateB point.s (lrCertificateY0 point)) *
        lrCertificateBDeriv point.s (lrCertificateY0 point)
          0 (lrCertificateY0DerivK point))
      (lrCertificateQPrime
          (lrCertificateB point.s (lrCertificateY0 point)) *
        lrCertificateBDeriv point.s (lrCertificateY0 point)
          0 (lrCertificateY0DerivChi point)) := by
    exact IntervalAD.contains_unary hqBValue hqPrimeBValue hb
  have hcoarse : lrQSecondCoarseCheck b.value = true := by
    have hraw :
        decide ((0 : ℚ) < b.value.lower ∧ b.value.lower ≤ b.value.upper ∧
          b.value.upper < 1) = true ∧
        certificate.qPrimeAtB.lowerEndpoint.primeCheck b.value.lower = true ∧
        certificate.qPrimeAtB.upperEndpoint.primeCheck b.value.upper = true := by
      simpa [LRQPrimeIntervalCertificate.check, and_assoc] using hparts.2
    simpa [lrQSecondCoarseCheck] using hraw.1
  have hqSecondB := lrQSecondCoarseEnclosure_sound hcoarse hb.1
  have hqPrimeB : qPrimeBAD.Contains
      (lrCertificateQPrime
        (lrCertificateB point.s (lrCertificateY0 point)))
      (lrCertificateQSecond
          (lrCertificateB point.s (lrCertificateY0 point)) *
        lrCertificateBDeriv point.s (lrCertificateY0 point)
          1 (lrCertificateY0DerivS point))
      (lrCertificateQSecond
          (lrCertificateB point.s (lrCertificateY0 point)) *
        lrCertificateBDeriv point.s (lrCertificateY0 point)
          0 (lrCertificateY0DerivK point))
      (lrCertificateQSecond
          (lrCertificateB point.s (lrCertificateY0 point)) *
        lrCertificateBDeriv point.s (lrCertificateY0 point)
          0 (lrCertificateY0DerivChi point)) := by
    exact IntervalAD.contains_unary hqPrimeBValue hqSecondB hb
  have hqYParts := certificate.qAtY.evaluateY0SK_sound terms
    hparts.1.2 hsPos hkPos hchi he hpoint
  have hqY : qY.Contains
      (lrCertificateQ (lrCertificateY0 point))
      (lrCertificateQPrime (lrCertificateY0 point) *
        lrCertificateY0DerivS point)
      (lrCertificateQPrime (lrCertificateY0 point) *
        lrCertificateY0DerivK point) 0 := by
    refine ⟨hqYParts.1, hqYParts.2.1, hqYParts.2.2, ?_⟩
    simp [qY, LRQZeroIntervalCertificate.evaluateY0SK,
      RationalEnclosure.point, RationalEnclosure.Contains]
  have honeMinusY := IntervalAD.contains_sub
    (IntervalAD.contains_const 1) hy
  have hfactor := IntervalAD.contains_mul hs honeMinusY
  have hcorrection := IntervalAD.contains_mul hfactor hqPrimeB
  have hresult := IntervalAD.contains_sub
    (IntervalAD.contains_sub hqB hqY) hcorrection
  refine ⟨?_, ?_, ?_⟩
  · convert hresult.1 using 1 <;>
      simp [evaluateY0SK, s, y, b, qPrimeB, qB, qY, qPrimeBAD,
        lrCertificateOmega] <;> ring
  · convert hresult.2.1 using 1 <;>
      simp [evaluateY0SK, s, y, b, qPrimeB, qB, qY, qPrimeBAD,
        lrCertificateOmegaDeriv, lrCertificateBDeriv] <;> ring
  · convert hresult.2.2.1 using 1 <;>
      simp [evaluateY0SK, s, y, b, qPrimeB, qB, qY, qPrimeBAD,
        lrCertificateOmegaDeriv, lrCertificateBDeriv] <;> ring

end LROmegaZeroIntervalCertificate
end CourtadeKumar
