import InformationTheory.CourtadeKumar.LRHighShapeVZeroFaceEvaluator

/-!
# Endpoint-safe smooth derivatives of `Q(χe)`

Although `Q'(χe)` is singular as `χ → 0`, its `s` and `k` chain-rule
factors are regular:

`Q'(χsk) χk = ((χsk) Q'(χsk)) / s`,

`Q'(χsk) χs = ((χsk) Q'(χsk)) / k`.

The zero-face `Q` certificate already encloses the regularized numerator
`y Q'(y)`.  This module divides that enclosure only by the positive smooth
coordinates, yielding an interval-AD node whose value, `s` derivative, and
`k` derivative remain valid on boxes touching `χ = 0`.  Its `χ` derivative
is deliberately synthetic and must not be used.
-/

namespace CourtadeKumar
namespace LRQZeroIntervalCertificate

/-- Endpoint-safe value and smooth-coordinate derivative enclosure for
`Q(χe)`.  The `derivChi` field is a dummy zero enclosure. -/
def evaluateY0SK (terms : ℕ) (box : CertificateBox)
    (certificate : LRQZeroIntervalCertificate) : IntervalAD :=
  let y0 := lrCertificateY0NonnegativeAD box
  let regularized := certificate.enclosure terms y0.value
  { value := regularized
    derivS := RationalEnclosure.div regularized box.sInterval
    derivK := RationalEnclosure.div regularized box.kInterval
    derivChi := RationalEnclosure.point 0 }

/-- Soundness of the value and the two smooth derivative fields.  No claim
is made that the synthetic `derivChi` field differentiates `Q(χe)`. -/
theorem evaluateY0SK_sound (terms : ℕ) {box : CertificateBox}
    {certificate : LRQZeroIntervalCertificate}
    (hcheck : certificate.check
      (lrCertificateY0NonnegativeAD box).value = true)
    (hsPos : (0 : ℚ) < box.sLo) (hkPos : (0 : ℚ) < box.kLo)
    (hchi : (0 : ℚ) ≤ box.chiLo)
    (he : (0 : ℚ) ≤ (lrCertificateEAD box).value.lower)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    let result := certificate.evaluateY0SK terms box
    result.value.Contains (lrCertificateQ (lrCertificateY0 point)) ∧
      result.derivS.Contains
        (lrCertificateQPrime (lrCertificateY0 point) *
          lrCertificateY0DerivS point) ∧
      result.derivK.Contains
        (lrCertificateQPrime (lrCertificateY0 point) *
          lrCertificateY0DerivK point) := by
  dsimp only
  let y0 := lrCertificateY0NonnegativeAD box
  let regularized := certificate.enclosure terms y0.value
  have hy0 := lrCertificateY0NonnegativeAD_sound hpoint hchi he
  have hvalue := certificate.sound terms hcheck hy0.1
  have hregularized := certificate.mul_prime_sound terms hcheck hy0.1
  have hs : box.sInterval.Contains point.s :=
    ⟨hpoint.1, hpoint.2.1⟩
  have hk : box.kInterval.Contains point.k :=
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hsPoint : 0 < point.s := by
    have hsLo : (0 : ℝ) < (box.sLo : ℝ) := by exact_mod_cast hsPos
    exact hsLo.trans_le hpoint.1
  have hkPoint : 0 < point.k := by
    have hkLo : (0 : ℝ) < (box.kLo : ℝ) := by exact_mod_cast hkPos
    exact hkLo.trans_le hpoint.2.2.1
  have hderivSRaw := RationalEnclosure.contains_div hsPos hregularized hs
  have hderivKRaw := RationalEnclosure.contains_div hkPos hregularized hk
  have hderivS :
      (RationalEnclosure.div regularized box.sInterval).Contains
        (lrCertificateQPrime (lrCertificateY0 point) *
          lrCertificateY0DerivS point) := by
    convert hderivSRaw using 1
    unfold lrCertificateY0 lrCertificateY0DerivS lrCertificateE
    field_simp [hsPoint.ne']
  have hderivK :
      (RationalEnclosure.div regularized box.kInterval).Contains
        (lrCertificateQPrime (lrCertificateY0 point) *
          lrCertificateY0DerivK point) := by
    convert hderivKRaw using 1
    unfold lrCertificateY0 lrCertificateY0DerivK lrCertificateE
    field_simp [hkPoint.ne']
  exact ⟨by simpa [evaluateY0SK, y0, regularized] using hvalue,
    by simpa [evaluateY0SK, y0, regularized] using hderivS,
    by simpa [evaluateY0SK, y0, regularized] using hderivK⟩

end LRQZeroIntervalCertificate
end CourtadeKumar
