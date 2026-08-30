import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACScalarSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRounding
import InformationTheory.CourtadeKumar.LRDeterminantAutoQCertificateCorrectness
import InformationTheory.CourtadeKumar.LRDeterminantFastQPointCertificate

/-!
# Shared point certificates for upper-`K` scalar values

The historical `A/C` point evaluator builds interval-AD certificates even
though its cached corner values only use `Q(z)` and `Q'(z)` at exact rational
points.  A single checked `LRQPointCertificate` already proves both facts.
This layer exposes that sharing and assembles the two scalar primitives from
small imported point enclosures.
-/

namespace CourtadeKumar
namespace LRUpperKPointCache

open Set
open LRUpperKReplayCertificate
open LRUpperKHistoricalACValues
open LRUpperKMidpointCoarsening

structure Values where
  q : RationalEnclosure
  qPrime : RationalEnclosure

structure Sound (terms : ℕ) (z : ℚ) (values : Values) : Prop where
  q : values.q.Contains (lrCertificateQ (z : ℝ))
  qPrime : values.qPrime.Contains (lrCertificateQPrime (z : ℝ))

/-- One serialized point certificate supplies both cached scalar nodes. -/
theorem sound_of_certificate (terms : ℕ) {z : ℚ}
    {certificate : LRQPointCertificate} {values : Values}
    (hz : z ∈ Ioo (0 : ℚ) 1)
    (hcheck : certificate.primeCheck z = true)
    (hq : Covers values.q (certificate.enclosure terms))
    (hqPrime : Covers values.qPrime (certificate.primeEnclosure terms)) :
    Sound terms z values := by
  have hparts : certificate.check z = true ∧
      (0 : ℚ) < certificate.sqrtEnclosure.lower := by
    simpa [LRQPointCertificate.primeCheck] using hcheck
  exact
    { q := contains_of_covers hq (certificate.sound terms
        hparts.1)
      qPrime := contains_of_covers hqPrime
        (certificate.prime_sound terms hz hcheck) }

/-- Compute one shared `Q/Q'` point entry directly.  Generated leaves prove
only the smaller `autoPrimeSucceeds` predicate, rather than unfolding the
full point checker or rebuilding separate interval-AD certificates. -/
def autoValues (bits terms sqrtFuel logFuel : ℕ) (z : ℚ) : Values :=
  let certificate := LRQPointCertificate.auto sqrtFuel logFuel z
  { q := LRUpperKDyadicOuterRounding.outerEnclosure bits
      (certificate.enclosure terms)
    qPrime := LRUpperKDyadicOuterRounding.outerEnclosure bits
      (certificate.primeEnclosure terms) }

theorem autoValues_sound (bits terms sqrtFuel logFuel : ℕ) {z : ℚ}
    (hz : z ∈ Ioo (0 : ℚ) 1)
    (hsucceeds : LRQPointCertificate.autoPrimeSucceeds
      sqrtFuel logFuel z = true) :
    Sound terms z (autoValues bits terms sqrtFuel logFuel z) := by
  apply sound_of_certificate terms hz
    (LRQPointCertificate.auto_primeCheck_of_succeeds
      sqrtFuel logFuel z hsucceeds)
  · simpa [autoValues] using
      LRUpperKDyadicOuterRounding.outerEnclosure_covers bits
        ((LRQPointCertificate.auto sqrtFuel logFuel z).enclosure terms)
  · simpa [autoValues] using
      LRUpperKDyadicOuterRounding.outerEnclosure_covers bits
        ((LRQPointCertificate.auto sqrtFuel logFuel z).primeEnclosure terms)

/-- Fast small-range values using the fixed polynomial square-root
certificate. -/
def fastAutoValues (bits terms logFuel : ℕ) (z : ℚ) : Values :=
  let certificate := LRQFastPointCertificate.auto logFuel z
  { q := LRUpperKDyadicOuterRounding.outerEnclosure bits
      (certificate.enclosure terms)
    qPrime := LRUpperKDyadicOuterRounding.outerEnclosure bits
      (certificate.primeEnclosure terms) }

theorem fastAutoValues_sound (bits terms logFuel : ℕ) {z : ℚ}
    (hz : z ∈ Ioo (0 : ℚ) 1)
    (hzUpper : z ≤ 1 / 16)
    (hsucceeds : LRQFastPointCertificate.autoPrimeSucceeds
      logFuel z = true) :
    Sound terms z (fastAutoValues bits terms logFuel z) := by
  apply sound_of_certificate terms hz
    (LRQFastPointCertificate.auto_primeCheck_of_succeeds
      logFuel hz.1.le hzUpper hsucceeds)
  · simpa [fastAutoValues] using
      LRUpperKDyadicOuterRounding.outerEnclosure_covers bits
        ((LRQFastPointCertificate.auto logFuel z).enclosure terms)
  · simpa [fastAutoValues] using
      LRUpperKDyadicOuterRounding.outerEnclosure_covers bits
        ((LRQFastPointCertificate.auto logFuel z).primeEnclosure terms)

def bPoint (s y : ℚ) : ℚ := s + (1 - s) * y

def omegaZero (s : ℚ) (atS : Values) : RationalEnclosure :=
  RationalEnclosure.sub atS.q
    (RationalEnclosure.mul (RationalEnclosure.point s) atS.qPrime)

def aEnclosure (s y : ℚ) (atB atS : Values) : RationalEnclosure :=
  if y = 0 then RationalEnclosure.point 0
  else
    RationalEnclosure.sub
      (RationalEnclosure.sub atB.q
        (RationalEnclosure.mul
          (RationalEnclosure.point (s * (1 - y))) atB.qPrime))
      (omegaZero s atS)

def cEnclosure (s y : ℚ) (atB atY atS : Values) : RationalEnclosure :=
  if y = 0 then RationalEnclosure.point 0
  else
    RationalEnclosure.sub
      (RationalEnclosure.sub
        (RationalEnclosure.sub atB.q atY.q)
        (RationalEnclosure.mul
          (RationalEnclosure.point (s * (1 - y))) atB.qPrime))
      (omegaZero s atS)

theorem aEnclosure_sound (terms : ℕ) {s y : ℚ}
    {atB atS : Values}
    (hb : Sound terms (bPoint s y) atB)
    (hs : Sound terms s atS) :
    (aEnclosure s y atB atS).Contains
      (aPrimitive (s : ℝ) (y : ℝ)) := by
  by_cases hy0 : y = 0
  · subst y
    simpa [aEnclosure, aPrimitive, lrCertificateQ_zero] using
      RationalEnclosure.contains_point (0 : ℚ)
  · have hbq : atB.q.Contains
        (lrCertificateQ (lrCertificateB (s : ℝ) (y : ℝ))) := by
      simpa [bPoint, lrCertificateB] using hb.q
    have hbqPrime : atB.qPrime.Contains
        (lrCertificateQPrime (lrCertificateB (s : ℝ) (y : ℝ))) := by
      simpa [bPoint, lrCertificateB] using hb.qPrime
    have hfactor :
        (RationalEnclosure.point (s * (1 - y))).Contains
          ((s : ℝ) * (1 - (y : ℝ))) := by
      simpa using RationalEnclosure.contains_point (s * (1 - y))
    have hcorrection := RationalEnclosure.contains_mul hfactor hbqPrime
    have hsFactor := RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point s) hs.qPrime
    have homegaZero := RationalEnclosure.contains_sub hs.q hsFactor
    have hresult := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_sub hbq hcorrection) homegaZero
    have hidentity :
        lrCertificateQ (lrCertificateB (s : ℝ) (y : ℝ)) -
              (s : ℝ) * (1 - (y : ℝ)) *
                lrCertificateQPrime (lrCertificateB (s : ℝ) (y : ℝ)) -
              (lrCertificateQ (s : ℝ) -
                (s : ℝ) * lrCertificateQPrime (s : ℝ)) =
            aPrimitive (s : ℝ) (y : ℝ) := by
      unfold aPrimitive lrCertificateOmega lrCertificateB
      rw [lrCertificateQ_zero]
      ring_nf
    rw [hidentity] at hresult
    simpa [aEnclosure, omegaZero, hy0] using hresult

theorem cEnclosure_sound (terms : ℕ) {s y : ℚ}
    {atB atY atS : Values}
    (hb : Sound terms (bPoint s y) atB)
    (hy : Sound terms y atY)
    (hs : Sound terms s atS) :
    (cEnclosure s y atB atY atS).Contains
      (cPrimitive (s : ℝ) (y : ℝ)) := by
  by_cases hy0 : y = 0
  · subst y
    simpa [cEnclosure, cPrimitive] using
      RationalEnclosure.contains_point (0 : ℚ)
  · have hbq : atB.q.Contains
        (lrCertificateQ (lrCertificateB (s : ℝ) (y : ℝ))) := by
      simpa [bPoint, lrCertificateB] using hb.q
    have hbqPrime : atB.qPrime.Contains
        (lrCertificateQPrime (lrCertificateB (s : ℝ) (y : ℝ))) := by
      simpa [bPoint, lrCertificateB] using hb.qPrime
    have hfactor :
        (RationalEnclosure.point (s * (1 - y))).Contains
          ((s : ℝ) * (1 - (y : ℝ))) := by
      simpa using RationalEnclosure.contains_point (s * (1 - y))
    have hcorrection := RationalEnclosure.contains_mul hfactor hbqPrime
    have hsFactor := RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point s) hs.qPrime
    have homegaZero := RationalEnclosure.contains_sub hs.q hsFactor
    have hresult := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_sub hbq hy.q) hcorrection)
      homegaZero
    have hidentity :
        lrCertificateQ (lrCertificateB (s : ℝ) (y : ℝ)) -
              lrCertificateQ (y : ℝ) -
              (s : ℝ) * (1 - (y : ℝ)) *
                lrCertificateQPrime (lrCertificateB (s : ℝ) (y : ℝ)) -
              (lrCertificateQ (s : ℝ) -
                (s : ℝ) * lrCertificateQPrime (s : ℝ)) =
            cPrimitive (s : ℝ) (y : ℝ) := by
      unfold cPrimitive lrCertificateOmega lrCertificateB
      rw [lrCertificateQ_zero]
      ring_nf
    rw [hidentity] at hresult
    simpa [cEnclosure, omegaZero, hy0] using hresult

end LRUpperKPointCache
end CourtadeKumar
