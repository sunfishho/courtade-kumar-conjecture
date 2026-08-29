import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACAD
import InformationTheory.CourtadeKumar.LRDeterminantUpperKACMonotonicity

/-!
# Scalar soundness for the historical fixed/moving upper-`K` nodes

This module supplies the purely interval-arithmetic layer behind the sharp
historical `A/C` derivative construction.  Its hypotheses deliberately expose
the checked `Q'` certificates, the value enclosures of the chart variables,
and the few nonnegative interval endpoints used by `mulNN`.  Consequently no
fact about a generated payload is trusted implicitly.

The two analytically refined nodes are handled in two stages:

* `fixedYPartialSRawI_sound` and `fixedEPartialSRawI_sound` prove soundness of
  the unmodified interval expressions;
* `fixedYPartialSI_sound` and `fixedEPartialSI_sound` then justify the
  intersection of the upper endpoint with zero by the checked theorem
  `LRUpperKReplayCertificate.fixedYPartialS_nonpos`.

All statements are scalar.  Downstream code may obtain the displayed value
containments from the corresponding `IntervalAD.Contains` statements simply
by taking their first projection.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKHistoricalFixedMovingSoundness

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD

/-! ## Small interval combinators -/

theorem mulNN_sound
    {a b : RationalEnclosure} {x y : ℝ}
    (haLower : (0 : ℚ) ≤ a.lower)
    (hbLower : (0 : ℚ) ≤ b.lower)
    (ha : a.Contains x) (hb : b.Contains y) :
    (mulNN a b).Contains (x * y) := by
  simpa [mulNN] using
    RationalEnclosure.contains_mulNonnegative haLower hbLower ha hb

theorem mulNN3_sound
    {a b c : RationalEnclosure} {x y z : ℝ}
    (haLower : (0 : ℚ) ≤ a.lower)
    (hbLower : (0 : ℚ) ≤ b.lower)
    (hcLower : (0 : ℚ) ≤ c.lower)
    (ha : a.Contains x) (hb : b.Contains y) (hc : c.Contains z) :
    (mulNN3 a b c).Contains (x * y * z) := by
  have habLower : (0 : ℚ) ≤ (mulNN a b).lower := by
    simpa [mulNN, RationalEnclosure.mulNonnegative] using
      mul_nonneg haLower hbLower
  have hab := mulNN_sound haLower hbLower ha hb
  simpa [mulNN3] using mulNN_sound habLower hcLower hab hc

theorem squareNN_sound
    {a : RationalEnclosure} {x : ℝ}
    (haLower : (0 : ℚ) ≤ a.lower)
    (ha : a.Contains x) :
    (squareNN a).Contains (x ^ 2) := by
  simpa [squareNN, pow_two] using
    mulNN_sound haLower haLower ha ha

/-- Intersecting an already sound interval with the analytic half-line
`(-∞,0]` is sound when the represented value is nonpositive. -/
theorem capUpperZero_sound
    {a : RationalEnclosure} {x : ℝ}
    (ha : a.Contains x) (hx : x ≤ 0) :
    (capUpperZero a).Contains x := by
  constructor
  · exact ha.1
  · change x ≤ ((min a.upper 0 : ℚ) : ℝ)
    rw [Rat.cast_min, Rat.cast_zero]
    exact le_min ha.2 hx

/-! ## Sharp `Q''` nodes -/

theorem qSecondAtSI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s : ℝ}
    (hcheck :
      payload.base.omegaZero.qPrimeAtS.value.check
        (sAD box).value = true)
    (hs : (sAD box).value.Contains s) :
    (qSecondAtSI terms box payload).Contains
      (lrCertificateQSecond s) := by
  exact LRQSharpSecondEnclosure.enclosure_sound terms hcheck hs

theorem qSecondAtBI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s y : ℝ}
    (hcheck :
      payload.base.omegaY0.qPrimeAtB.check
        (y0BAd box).value = true)
    (hb : (y0BAd box).value.Contains (lrCertificateB s y)) :
    (qSecondAtBI terms box payload).Contains
      (lrCertificateQSecond (lrCertificateB s y)) := by
  exact LRQSharpSecondEnclosure.enclosure_sound terms hcheck hb

theorem qSecondAtEBI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s e : ℝ}
    (hcheck :
      payload.base.omegaE.qPrimeAtB.value.check
        (eBAd box).value = true)
    (hb : (eBAd box).value.Contains (lrCertificateB s e)) :
    (qSecondAtEBI terms box payload).Contains
      (lrCertificateQSecond (lrCertificateB s e)) := by
  exact LRQSharpSecondEnclosure.enclosure_sound terms hcheck hb

/-! ## Fixed-`y` contribution -/

theorem fixedYPartialSRawI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s y : ℝ}
    (hcheckS :
      payload.base.omegaZero.qPrimeAtS.value.check
        (sAD box).value = true)
    (hcheckB :
      payload.base.omegaY0.qPrimeAtB.check
        (y0BAd box).value = true)
    (hs : (sAD box).value.Contains s)
    (hy : (y0AD box).value.Contains y)
    (hb : (y0BAd box).value.Contains (lrCertificateB s y))
    (honeMinusYLower : (0 : ℚ) ≤ (oneMinusYI box).lower) :
    (fixedYPartialSRawI terms box payload).Contains
      (s * (lrCertificateQSecond s -
        (1 - y) ^ 2 *
          lrCertificateQSecond (lrCertificateB s y))) := by
  have hqS := qSecondAtSI_sound terms hcheckS hs
  have hqB := qSecondAtBI_sound terms hcheckB hb
  have honeMinusY : (oneMinusYI box).Contains (1 - y) := by
    simpa [oneMinusYI] using RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) hy
  have honeMinusYSquare :=
    squareNN_sound honeMinusYLower honeMinusY
  have hweighted :=
    RationalEnclosure.contains_mul honeMinusYSquare hqB
  have hdiff := RationalEnclosure.contains_sub hqS hweighted
  simpa [fixedYPartialSRawI] using
    RationalEnclosure.contains_mul hs hdiff

theorem fixedYPartialSI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s y : ℝ}
    (hcheckS :
      payload.base.omegaZero.qPrimeAtS.value.check
        (sAD box).value = true)
    (hcheckB :
      payload.base.omegaY0.qPrimeAtB.check
        (y0BAd box).value = true)
    (hs : (sAD box).value.Contains s)
    (hy : (y0AD box).value.Contains y)
    (hb : (y0BAd box).value.Contains (lrCertificateB s y))
    (honeMinusYLower : (0 : ℚ) ≤ (oneMinusYI box).lower)
    (hsPhysical : s ∈ Ioo (0 : ℝ) 1)
    (hyPhysical : y ∈ Ico (0 : ℝ) 1) :
    (fixedYPartialSI terms box payload).Contains
      (s * (lrCertificateQSecond s -
        (1 - y) ^ 2 *
          lrCertificateQSecond (lrCertificateB s y))) := by
  have hraw := fixedYPartialSRawI_sound terms hcheckS hcheckB
    hs hy hb honeMinusYLower
  have hnonpos := fixedYPartialS_nonpos hsPhysical hyPhysical
  exact capUpperZero_sound hraw hnonpos

/-! ## Moving-`y` coefficient -/

theorem movingYCoefficientI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s y : ℝ}
    (hcheckB :
      payload.base.omegaY0.qPrimeAtB.check
        (y0BAd box).value = true)
    (hs : (sAD box).value.Contains s)
    (hy : (y0AD box).value.Contains y)
    (hb : (y0BAd box).value.Contains (lrCertificateB s y))
    (hsLower : (0 : ℚ) ≤ (sAD box).value.lower)
    (honeMinusSLower : (0 : ℚ) ≤ (oneMinusSI box).lower)
    (honeMinusYLower : (0 : ℚ) ≤ (oneMinusYI box).lower) :
    (movingYCoefficientI terms box payload).Contains
      (lrCertificateQPrime (lrCertificateB s y) -
        s * (1 - s) * (1 - y) *
          lrCertificateQSecond (lrCertificateB s y)) := by
  have honeMinusS : (oneMinusSI box).Contains (1 - s) := by
    simpa [oneMinusSI] using RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) hs
  have honeMinusY : (oneMinusYI box).Contains (1 - y) := by
    simpa [oneMinusYI] using RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) hy
  have hfactor := mulNN3_sound hsLower honeMinusSLower
    honeMinusYLower hs honeMinusS honeMinusY
  have hqPrime := payload.base.omegaY0.qPrimeAtB.sound
    terms hcheckB hb
  have hqSecond := qSecondAtBI_sound terms hcheckB hb
  have hcorrection := RationalEnclosure.contains_mul hfactor hqSecond
  simpa [movingYCoefficientI] using
    RationalEnclosure.contains_sub hqPrime hcorrection

/-! ## Fixed-`e` contribution -/

theorem fixedEPartialSRawI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s e : ℝ}
    (hcheckS :
      payload.base.omegaZero.qPrimeAtS.value.check
        (sAD box).value = true)
    (hcheckB :
      payload.base.omegaE.qPrimeAtB.value.check
        (eBAd box).value = true)
    (hs : (sAD box).value.Contains s)
    (he : (eAD box).value.Contains e)
    (hb : (eBAd box).value.Contains (lrCertificateB s e))
    (honeMinusELower : (0 : ℚ) ≤ (oneMinusEI box).lower) :
    (fixedEPartialSRawI terms box payload).Contains
      (s * (lrCertificateQSecond s -
        (1 - e) ^ 2 *
          lrCertificateQSecond (lrCertificateB s e))) := by
  have hqS := qSecondAtSI_sound terms hcheckS hs
  have hqB := qSecondAtEBI_sound terms hcheckB hb
  have honeMinusE : (oneMinusEI box).Contains (1 - e) := by
    simpa [oneMinusEI] using RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) he
  have honeMinusESquare :=
    squareNN_sound honeMinusELower honeMinusE
  have hweighted :=
    RationalEnclosure.contains_mul honeMinusESquare hqB
  have hdiff := RationalEnclosure.contains_sub hqS hweighted
  simpa [fixedEPartialSRawI] using
    RationalEnclosure.contains_mul hs hdiff

theorem fixedEPartialSI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s e : ℝ}
    (hcheckS :
      payload.base.omegaZero.qPrimeAtS.value.check
        (sAD box).value = true)
    (hcheckB :
      payload.base.omegaE.qPrimeAtB.value.check
        (eBAd box).value = true)
    (hs : (sAD box).value.Contains s)
    (he : (eAD box).value.Contains e)
    (hb : (eBAd box).value.Contains (lrCertificateB s e))
    (honeMinusELower : (0 : ℚ) ≤ (oneMinusEI box).lower)
    (hsPhysical : s ∈ Ioo (0 : ℝ) 1)
    (hePhysical : e ∈ Ico (0 : ℝ) 1) :
    (fixedEPartialSI terms box payload).Contains
      (s * (lrCertificateQSecond s -
        (1 - e) ^ 2 *
          lrCertificateQSecond (lrCertificateB s e))) := by
  have hraw := fixedEPartialSRawI_sound terms hcheckS hcheckB
    hs he hb honeMinusELower
  have hnonpos := fixedYPartialS_nonpos hsPhysical hePhysical
  exact capUpperZero_sound hraw hnonpos

/-! ## Moving-`e` coefficient -/

theorem movingECoefficientI_sound (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {s e : ℝ}
    (hcheckB :
      payload.base.omegaE.qPrimeAtB.value.check
        (eBAd box).value = true)
    (hs : (sAD box).value.Contains s)
    (he : (eAD box).value.Contains e)
    (hb : (eBAd box).value.Contains (lrCertificateB s e))
    (hsLower : (0 : ℚ) ≤ (sAD box).value.lower)
    (honeMinusSLower : (0 : ℚ) ≤ (oneMinusSI box).lower)
    (honeMinusELower : (0 : ℚ) ≤ (oneMinusEI box).lower) :
    (movingECoefficientI terms box payload).Contains
      (lrCertificateQPrime (lrCertificateB s e) -
        s * (1 - s) * (1 - e) *
          lrCertificateQSecond (lrCertificateB s e)) := by
  have honeMinusS : (oneMinusSI box).Contains (1 - s) := by
    simpa [oneMinusSI] using RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) hs
  have honeMinusE : (oneMinusEI box).Contains (1 - e) := by
    simpa [oneMinusEI] using RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) he
  have hfactor := mulNN3_sound hsLower honeMinusSLower
    honeMinusELower hs honeMinusS honeMinusE
  have hqPrime := payload.base.omegaE.qPrimeAtB.value.sound
    terms hcheckB hb
  have hqSecond := qSecondAtEBI_sound terms hcheckB hb
  have hcorrection := RationalEnclosure.contains_mul hfactor hqSecond
  simpa [movingECoefficientI] using
    RationalEnclosure.contains_sub hqPrime hcorrection

end LRUpperKHistoricalFixedMovingSoundness
end CourtadeKumar
