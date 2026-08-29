import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACAD

/-!
# Sound regularized `Q(y0)` and chart-coordinate partials

This module supplies the semantic layer for the endpoint-safe pieces of the
historical three-coordinate upper-`K` evaluator.  It deliberately stops
before the `A/C` chain rule: the results here require only the already checked
base payload, the regularized `Q'` endpoint payload, and the checked enclosure
of `sqrt(e)`.

For a chart coordinate `(s,K,h)` and its decoded physical point, the exact
quantities are

* `e = s^2 K`,
* `y0 = h^2 e`,
* `partial_s y0 = 2 y0 / s`,
* `partial_K y0 = y0 / K`, and
* `partial_h y0 = 2 h e`.

The first two `Q(y0)` partials use the regularized scale `y0 * Q'(y0)`.
The third uses `sqrt(e) * (sqrt(y0) * Q'(y0))`; this is the continuous
zero-face representation used by the historical checker.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalACAD

open LRUpperKReplayCertificate

/-! ## Boolean-check extraction -/

/-- The four facts checked by `auxiliaryCheck`, exposed without asking later
soundness proofs to depend on the Boolean conjunction's association. -/
structure AuxiliaryValid (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Prop where
  qY0ScaleCheck :
    (qY0ScaleCertificate payload).check terms (y0AD box).value = true
  sqrtECheck : payload.sqrtE.check (eAD box).value = true
  qPrimeAtSCheck :
    payload.base.omegaZero.qPrimeAtS.value.check (sAD box).value = true
  qPrimeAtBCheck :
    payload.base.omegaY0.qPrimeAtB.check (y0BAd box).value = true

theorem auxiliaryCheck_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload}
    (hcheck : auxiliaryCheck terms box payload = true) :
    AuxiliaryValid terms box payload := by
  have hparts :
      (((qY0ScaleCertificate payload).check terms (y0AD box).value = true ∧
          payload.sqrtE.check (eAD box).value = true) ∧
        payload.base.omegaZero.qPrimeAtS.value.check
          (sAD box).value = true) ∧
      payload.base.omegaY0.qPrimeAtB.check (y0BAd box).value = true := by
    simpa [auxiliaryCheck] using hcheck
  exact
    { qY0ScaleCheck := hparts.1.1.1
      sqrtECheck := hparts.1.1.2
      qPrimeAtSCheck := hparts.1.2
      qPrimeAtBCheck := hparts.2 }

/-- All physical and auxiliary facts certified by the full sharp checker. -/
structure Valid (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Prop where
  base : LRUpperKReplayCertificate.Valid box payload.base
  auxiliary : AuxiliaryValid terms box payload

theorem check_sound {terms : ℕ} {box : CertificateBox} {payload : Payload}
    (hcheck : check terms box payload = true) :
    Valid terms box payload := by
  have hparts :
      LRUpperKReplayCertificate.payloadCheck box payload.base = true ∧
        auxiliaryCheck terms box payload = true := by
    simpa [check] using hcheck
  exact
    { base := LRUpperKReplayCertificate.payloadCheck_sound hparts.1
      auxiliary := auxiliaryCheck_sound hparts.2 }

/-! ## Nonnegative endpoint consequences -/

private theorem sqrtCertificate_lower_nonnegative
    {input : RationalEnclosure}
    {certificate : RationalEnclosure.SqrtCertificate}
    (hcheck : certificate.check input = true) :
    (0 : ℚ) ≤ certificate.enclosure.lower := by
  have hparts :
      (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
        (0 : ℚ) ≤ certificate.lower ∧
        certificate.lower ^ 2 ≤ input.lower ∧
        (0 : ℚ) ≤ certificate.upper ∧
        input.upper ≤ certificate.upper ^ 2 := by
    simpa [RationalEnclosure.SqrtCertificate.check] using hcheck
  simpa [RationalEnclosure.SqrtCertificate.enclosure] using hparts.2.2.1

/-- The lower endpoint of the checked regularized square-root scale is
nonnegative.  This is the side condition needed to justify the historical
nonnegative-product interval operation in the `h` partial. -/
private theorem sqrtMulPrimeEnclosure_lower_nonnegative
    (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQRegularizedScaleCertificate}
    (hcheck : certificate.check terms input = true) :
    (0 : ℚ) ≤
      (certificate.sqrtMulPrimeEnclosure terms input).lower := by
  by_cases hu0 : input.upper = 0
  · simp [LRQRegularizedScaleCertificate.sqrtMulPrimeEnclosure, hu0,
      RationalEnclosure.point]
  · have hraw :
        decide ((0 : ℚ) ≤ input.lower ∧
            input.lower ≤ input.upper ∧ input.upper < 1) = true ∧
          (LRQRegularizedScaleCertificate.endpointCheck terms input.upper
              certificate.upper certificate.sqrtUpper &&
            if input.lower = 0 then true
            else LRQRegularizedScaleCertificate.endpointCheck terms input.lower
              certificate.lower certificate.sqrtLower) = true := by
      simpa [LRQRegularizedScaleCertificate.check, hu0] using hcheck
    have hendpoints :
        LRQRegularizedScaleCertificate.endpointCheck terms input.upper
            certificate.upper certificate.sqrtUpper = true ∧
          (if input.lower = 0 then true
           else LRQRegularizedScaleCertificate.endpointCheck terms input.lower
             certificate.lower certificate.sqrtLower) = true := by
      simpa [hu0] using hraw.2
    by_cases hl0 : input.lower = 0
    · simp [LRQRegularizedScaleCertificate.sqrtMulPrimeEnclosure,
        hu0, hl0]
    · have hlcheck :
          LRQRegularizedScaleCertificate.endpointCheck terms input.lower
              certificate.lower certificate.sqrtLower = true := by
        simpa [hl0] using hendpoints.2
      have hlparts :
          (certificate.lower.primeCheck input.lower = true ∧
              certificate.sqrtLower.check
                (RationalEnclosure.point input.lower) = true) ∧
            decide ((0 : ℚ) ≤
              (certificate.lower.primeEnclosure terms).lower) = true := by
        simpa [LRQRegularizedScaleCertificate.endpointCheck] using hlcheck
      have hsqrtLower :
          (0 : ℚ) ≤ certificate.sqrtLower.enclosure.lower :=
        sqrtCertificate_lower_nonnegative hlparts.1.2
      have hprimeLower :
          (0 : ℚ) ≤ (certificate.lower.primeEnclosure terms).lower := by
        simpa using hlparts.2
      simpa [LRQRegularizedScaleCertificate.sqrtMulPrimeEnclosure,
          LRQRegularizedScaleCertificate.sqrtMulPrimeEndpointEnclosure,
          RationalEnclosure.mulNonnegative, hu0, hl0] using
        mul_nonneg hsqrtLower hprimeLower

/-! ## Exact chart-value enclosures -/

private theorem sValue_sound {box : CertificateBox}
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (sAD box).value.Contains coordinate.s := by
  exact (IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)).1

private theorem ratioValue_sound {box : CertificateBox}
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (ratioAD box).value.Contains coordinate.k := by
  exact (IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)).1

private theorem hValue_sound {box : CertificateBox}
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (hAD box).value.Contains coordinate.chi := by
  exact (IntervalAD.contains_variableChi
    (show box.chiInterval.Contains coordinate.chi from
      ⟨hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩)).1

/-- Full value-and-partial containment for `e=s^2 K`, factored out because
both the square-root certificate and the exact `h` partial consume it. -/
theorem eAD_sound {terms : ℕ} {box : CertificateBox} {payload : Payload}
    (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let eS := raw.k + raw.s * coordinate.k
    let eK := raw.s * coordinate.s
    (eAD box).Contains (lrCertificateE raw) eS eK 0 := by
  dsimp only
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.base.sPositive.le hvalid.base.ratioPositive.le
  have hkRaw := mulNonnegativeAD_sound hvalid.base.sPositive.le
    hvalid.base.ratioPositive.le hs hratio
  have heRaw := mulNonnegativeAD_sound hvalid.base.sPositive.le hkLower hs hkRaw
  convert heRaw using 1 <;>
    simp [raw, eS, eK, lrDeterminantKChartDecode] <;> ring

theorem eValue_sound {terms : ℕ} {box : CertificateBox} {payload : Payload}
    (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (eAD box).value.Contains
      (lrCertificateE (lrDeterminantKChartDecode coordinate)) := by
  exact (eAD_sound hvalid hcoordinate).1

theorem y0Value_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (y0AD box).value.Contains
      (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := by
  exact (LRUpperKReplayCertificate.y0AD_sound
    hvalid.base hcoordinate).1

/-! ## Regularized scalar enclosures -/

theorem y0MulPrimeI_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (y0MulPrimeI terms box payload).Contains
      (lrCertificateQMulPrime
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
  exact LRQRegularizedScaleCertificate.mulPrime_sound terms
    hvalid.auxiliary.qY0ScaleCheck (y0Value_sound hvalid hcoordinate)

theorem y0SqrtMulPrimeI_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (y0SqrtMulPrimeI terms box payload).Contains
      (lrCertificateQSqrtMulPrime
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
  exact LRQRegularizedScaleCertificate.sqrtMulPrime_sound terms
    hvalid.auxiliary.qY0ScaleCheck (y0Value_sound hvalid hcoordinate)

theorem sqrtEI_sound {terms : ℕ} {box : CertificateBox} {payload : Payload}
    (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (sqrtEI payload).Contains
      (Real.sqrt (lrCertificateE
        (lrDeterminantKChartDecode coordinate))) := by
  exact payload.sqrtE.sound hvalid.auxiliary.sqrtECheck
    (eValue_sound hvalid hcoordinate)

/-! ## Sound `Q(y0)` chart partials -/

theorem qPartialSI_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (qPartialSI terms box payload).Contains
      (2 * (lrCertificateY0 (lrDeterminantKChartDecode coordinate) *
          lrCertificateQPrime
            (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) /
        coordinate.s) := by
  have hscaled := RationalEnclosure.contains_scale (2 : ℚ)
    (y0MulPrimeI_sound terms hvalid hcoordinate)
  have hdiv := RationalEnclosure.contains_div hvalid.base.sPositive hscaled
    (sValue_sound hcoordinate)
  simpa [qPartialSI, lrCertificateQMulPrime] using hdiv

theorem qPartialKI_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (qPartialKI terms box payload).Contains
      ((lrCertificateY0 (lrDeterminantKChartDecode coordinate) *
          lrCertificateQPrime
            (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) /
        coordinate.k) := by
  have hdiv := RationalEnclosure.contains_div hvalid.base.ratioPositive
    (y0MulPrimeI_sound terms hvalid hcoordinate)
    (ratioValue_sound hcoordinate)
  simpa [qPartialKI, lrCertificateQMulPrime] using hdiv

/-- Soundness of the zero-face regularized `h` partial.  The right-hand side
is kept in its historical square-root factorization; identifying it with
`2*h*e*Q'(y0)` is a separate elementary physical-domain identity. -/
theorem qPartialHI_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (qPartialHI terms box payload).Contains
      ((2 : ℝ) *
        Real.sqrt (lrCertificateE (lrDeterminantKChartDecode coordinate)) *
        (Real.sqrt
            (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) *
          lrCertificateQPrime
            (lrCertificateY0 (lrDeterminantKChartDecode coordinate)))) := by
  have hsqrtE := sqrtEI_sound hvalid hcoordinate
  have hsqrtQ := y0SqrtMulPrimeI_sound terms hvalid hcoordinate
  have hsqrtELower : (0 : ℚ) ≤ (sqrtEI payload).lower := by
    simpa [sqrtEI] using
      sqrtCertificate_lower_nonnegative hvalid.auxiliary.sqrtECheck
  have hsqrtQLower :
      (0 : ℚ) ≤ (y0SqrtMulPrimeI terms box payload).lower := by
    simpa [y0SqrtMulPrimeI] using
      sqrtMulPrimeEnclosure_lower_nonnegative terms
        hvalid.auxiliary.qY0ScaleCheck
  have htwoLower :
      (0 : ℚ) ≤ (RationalEnclosure.point 2).lower := by
    norm_num [RationalEnclosure.point]
  have hfirst := RationalEnclosure.contains_mulNonnegative
    htwoLower hsqrtELower (RationalEnclosure.contains_point 2) hsqrtE
  have hfirstLower :
      (0 : ℚ) ≤
        (mulNN (RationalEnclosure.point 2) (sqrtEI payload)).lower := by
    change (0 : ℚ) ≤ 2 * (sqrtEI payload).lower
    exact mul_nonneg (by norm_num) hsqrtELower
  have hresult := RationalEnclosure.contains_mulNonnegative
    hfirstLower hsqrtQLower hfirst hsqrtQ
  simpa [qPartialHI, mulNN3, mulNN, lrCertificateQSqrtMulPrime] using
    hresult

/-- The square-root factorization in `qPartialHI_sound` is exactly the true
chart `h` derivative, including at `h=0`. -/
theorem qPartialHI_sound_exact (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (qPartialHI terms box payload).Contains
      ((2 : ℝ) * coordinate.chi *
        lrCertificateE (lrDeterminantKChartDecode coordinate) *
        lrCertificateQPrime
          (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
  have hhValue := hValue_sound hcoordinate
  have heValue := eValue_sound hvalid hcoordinate
  have hhNonnegative : (0 : ℝ) ≤ coordinate.chi := by
    have hlower : (0 : ℝ) ≤ ((hAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.base.hNonnegative
    exact hlower.trans hhValue.1
  have heNonnegative :
      (0 : ℝ) ≤
        lrCertificateE (lrDeterminantKChartDecode coordinate) := by
    have hlower : (0 : ℝ) ≤ ((eAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.base.ePositive.le
    exact hlower.trans heValue.1
  have hyIdentity :
      lrCertificateY0 (lrDeterminantKChartDecode coordinate) =
        coordinate.chi ^ 2 *
          lrCertificateE (lrDeterminantKChartDecode coordinate) := by
    simp [lrCertificateY0, lrDeterminantKChartDecode]
  have hsqrtY :
      Real.sqrt
          (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) =
        coordinate.chi *
          Real.sqrt
            (lrCertificateE (lrDeterminantKChartDecode coordinate)) := by
    rw [hyIdentity, Real.sqrt_mul (sq_nonneg coordinate.chi),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hhNonnegative]
  have hfactorization :
      (2 : ℝ) *
          Real.sqrt (lrCertificateE
            (lrDeterminantKChartDecode coordinate)) *
          (Real.sqrt
              (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) *
            lrCertificateQPrime
              (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) =
        2 * coordinate.chi *
          lrCertificateE (lrDeterminantKChartDecode coordinate) *
          lrCertificateQPrime
            (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := by
    rw [hsqrtY]
    calc
      2 * Real.sqrt
            (lrCertificateE (lrDeterminantKChartDecode coordinate)) *
            (coordinate.chi *
                Real.sqrt
                  (lrCertificateE (lrDeterminantKChartDecode coordinate)) *
              lrCertificateQPrime
                (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) =
          2 * coordinate.chi *
            (Real.sqrt
                (lrCertificateE (lrDeterminantKChartDecode coordinate)) *
              Real.sqrt
                (lrCertificateE (lrDeterminantKChartDecode coordinate))) *
            lrCertificateQPrime
              (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := by
            ring
      _ = 2 * coordinate.chi *
            lrCertificateE (lrDeterminantKChartDecode coordinate) *
            lrCertificateQPrime
              (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := by
            rw [Real.mul_self_sqrt heNonnegative]
  rw [← hfactorization]
  exact qPartialHI_sound terms hvalid hcoordinate

/-! ## Sound exact chart partials of `y0` -/

theorem yPartialSI_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (yPartialSI box).Contains
      (2 * lrCertificateY0 (lrDeterminantKChartDecode coordinate) /
        coordinate.s) := by
  have hscaled := RationalEnclosure.contains_scale (2 : ℚ)
    (y0Value_sound hvalid hcoordinate)
  have hdiv := RationalEnclosure.contains_div hvalid.base.sPositive hscaled
    (sValue_sound hcoordinate)
  simpa [yPartialSI] using hdiv

theorem yPartialKI_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (yPartialKI box).Contains
      (lrCertificateY0 (lrDeterminantKChartDecode coordinate) /
        coordinate.k) := by
  have hdiv := RationalEnclosure.contains_div hvalid.base.ratioPositive
    (y0Value_sound hvalid hcoordinate) (ratioValue_sound hcoordinate)
  simpa [yPartialKI] using hdiv

theorem yPartialHI_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hvalid : Valid terms box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (yPartialHI box).Contains
      ((2 : ℝ) * coordinate.chi *
        lrCertificateE (lrDeterminantKChartDecode coordinate)) := by
  have hh := hValue_sound hcoordinate
  have he := eValue_sound hvalid hcoordinate
  have htwoLower :
      (0 : ℚ) ≤ (RationalEnclosure.point 2).lower := by
    norm_num [RationalEnclosure.point]
  have hfirst := RationalEnclosure.contains_mulNonnegative
    htwoLower hvalid.base.hNonnegative
    (RationalEnclosure.contains_point 2) hh
  have hfirstLower :
      (0 : ℚ) ≤
        (mulNN (RationalEnclosure.point 2) (hAD box).value).lower := by
    change (0 : ℚ) ≤ 2 * (hAD box).value.lower
    exact mul_nonneg (by norm_num) hvalid.base.hNonnegative
  have hresult := RationalEnclosure.contains_mulNonnegative
    hfirstLower hvalid.base.ePositive.le hfirst he
  simpa [yPartialHI, mulNN3, mulNN] using hresult

end LRUpperKHistoricalACAD
end CourtadeKumar
