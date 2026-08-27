import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Value-only endpoint enclosure for the LR noise kernel

The derivative of `Q(y)` is singular at `y = 0`, although the noise kernel
`omega_s(y)` itself has a finite value there.  This module evaluates only
the value interval.  It combines the zero-endpoint `Q` enclosure with the
ordinary interior enclosures for `Q(b_s(y))` and `Q'(b_s(y))`.
-/

namespace CourtadeKumar

structure LROmegaZeroIntervalCertificate where
  qAtB : LRQIntervalCertificate
  qAtY : LRQZeroIntervalCertificate
  qPrimeAtB : LRQPrimeIntervalCertificate

namespace LROmegaZeroIntervalCertificate

def check (s y : IntervalAD)
    (certificate : LROmegaZeroIntervalCertificate) : Bool :=
  let b := lrCertificateBAD s y
  certificate.qAtB.check b.value &&
    certificate.qAtY.check y.value &&
    certificate.qPrimeAtB.check b.value

def evaluate (terms : ℕ) (s y : IntervalAD)
    (certificate : LROmegaZeroIntervalCertificate) : RationalEnclosure :=
  let qB := certificate.qAtB.enclosure terms
  let qY := certificate.qAtY.enclosure terms y.value
  let qPrimeB := certificate.qPrimeAtB.enclosure terms
  RationalEnclosure.sub (RationalEnclosure.sub qB qY)
    (RationalEnclosure.mul
      (RationalEnclosure.mul s.value
        (RationalEnclosure.sub (RationalEnclosure.point 1) y.value))
      qPrimeB)

theorem sound (terms : ℕ) {sAD yAD : IntervalAD}
    {s y sS sK sChi yS yK yChi : ℝ}
    {certificate : LROmegaZeroIntervalCertificate}
    (hcheck : certificate.check sAD yAD = true)
    (hs : sAD.Contains s sS sK sChi)
    (hy : yAD.Contains y yS yK yChi) :
    (certificate.evaluate terms sAD yAD).Contains
      (lrCertificateOmega s y) := by
  let b := lrCertificateBAD sAD yAD
  have hparts :
      (certificate.qAtB.check b.value = true ∧
        certificate.qAtY.check yAD.value = true) ∧
        certificate.qPrimeAtB.check b.value = true := by
    simpa [check, b] using hcheck
  have hbAD := lrCertificateBAD_sound hs hy
  have hb : b.value.Contains (lrCertificateB s y) := by
    simpa [b] using hbAD.1
  have hqB := certificate.qAtB.sound terms hparts.1.1 hb
  have hqY := certificate.qAtY.sound terms hparts.1.2 hy.1
  have hqPrimeB := certificate.qPrimeAtB.sound terms hparts.2 hb
  have honeMinusY := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hy.1
  have hfactor := RationalEnclosure.contains_mul hs.1 honeMinusY
  have hcorrection := RationalEnclosure.contains_mul hfactor hqPrimeB
  have hresult := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_sub hqB hqY) hcorrection
  simpa [evaluate, lrCertificateOmega] using hresult

def auto (sqrtFuel logFuel : ℕ) (s y : IntervalAD) :
    LROmegaZeroIntervalCertificate :=
  let b := lrCertificateBAD s y
  { qAtB := LRQIntervalCertificate.auto sqrtFuel logFuel b.value
    qAtY := LRQZeroIntervalCertificate.auto sqrtFuel logFuel y.value
    qPrimeAtB := LRQPrimeIntervalCertificate.auto sqrtFuel logFuel b.value }

end LROmegaZeroIntervalCertificate
end CourtadeKumar
