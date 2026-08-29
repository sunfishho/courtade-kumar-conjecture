import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACValues

/-!
# Soundness of the historical scalar `A/C` point nodes

The point evaluator has an exact endpoint branch at `y = 0`.  At a positive
rational point, its payload is checked by the ordinary interval-AD omega
certificates.  The `C` enclosure is their direct value difference.  The `A`
enclosure exposes the cancellation

`Q(b) - s(1-y)Q'(b) - omega_s(0)`

before interval evaluation; the final algebraic identity identifies this
with `Q(y) + omega_s(y) - omega_s(0)`.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalACValues

open LRUpperKReplayCertificate

private theorem constAD_sound (q : ℚ) :
    (constAD q).Contains (q : ℝ) 0 0 0 := by
  simpa [constAD] using IntervalAD.contains_const q

private theorem scalarCheck_parts_of_ne
    {s y : ℚ} {payload : ScalarPayload}
    (hy0 : y ≠ 0) (hcheck : scalarCheck s y payload = true) :
    payload.omegaY.check (constAD s) (constAD y) = true ∧
      payload.omegaZero.check (constAD s) = true := by
  simpa [scalarCheck, hy0] using hcheck

/-- The cancellation-free historical scalar node encloses `A_s(y)` at every
checked rational point, including the exact endpoint `y = 0`. -/
theorem aScalarI_sound (terms : ℕ) {s y : ℚ} {payload : ScalarPayload}
    (hcheck : scalarCheck s y payload = true) :
    (aScalarI terms s y payload).Contains
      (aPrimitive (s : ℝ) (y : ℝ)) := by
  by_cases hy0 : y = 0
  · subst y
    simpa [aScalarI, aPrimitive, lrCertificateQ_zero] using
      RationalEnclosure.contains_point (0 : ℚ)
  · have hchecks := scalarCheck_parts_of_ne hy0 hcheck
    have hs := constAD_sound s
    have hy := constAD_sound y
    let bAD := lrCertificateBAD (constAD s) (constAD y)
    have hbAD := lrCertificateBAD_sound hs hy
    have hOmegaParts :
        (payload.omegaY.qAtB.check bAD.value = true ∧
          payload.omegaY.qAtY.check (constAD y).value = true) ∧
          payload.omegaY.qPrimeAtB.check bAD.value = true := by
      simpa [LROmegaADCertificate.check, bAD] using hchecks.1
    have hqBFull := payload.omegaY.qAtB.sound terms
      hOmegaParts.1.1 hbAD
    have hqPrimeBFull := payload.omegaY.qPrimeAtB.sound terms
      hOmegaParts.2 hbAD
    have hqB :
        (payload.omegaY.qAtB.value.enclosure terms).Contains
          (lrCertificateQ (lrCertificateB (s : ℝ) (y : ℝ))) := by
      simpa [LRQADCertificate.evaluate, IntervalAD.unary] using hqBFull.1
    have hqPrimeB :
        (payload.omegaY.qPrimeAtB.value.enclosure terms).Contains
          (lrCertificateQPrime
            (lrCertificateB (s : ℝ) (y : ℝ))) := by
      simpa [LRQPrimeADCertificate.evaluate, IntervalAD.unary] using
        hqPrimeBFull.1
    have hfactor :
        (RationalEnclosure.point (s * (1 - y))).Contains
          ((s : ℝ) * (1 - (y : ℝ))) := by
      simpa using RationalEnclosure.contains_point (s * (1 - y))
    have hcorrection := RationalEnclosure.contains_mul hfactor hqPrimeB
    have hwFull := payload.omegaZero.sound terms hchecks.2 hs
    have hresult := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_sub hqB hcorrection) hwFull.1
    have hidentity :
        lrCertificateQ (lrCertificateB (s : ℝ) (y : ℝ)) -
              (s : ℝ) * (1 - (y : ℝ)) *
                lrCertificateQPrime
                  (lrCertificateB (s : ℝ) (y : ℝ)) -
              lrCertificateOmega (s : ℝ) 0 =
            aPrimitive (s : ℝ) (y : ℝ) := by
      unfold aPrimitive lrCertificateOmega
      ring
    rw [hidentity] at hresult
    simpa [aScalarI, hy0] using hresult

/-- The historical scalar `C` node is the checked difference
`omega_s(y) - omega_s(0)`, with an exact endpoint branch at `y = 0`. -/
theorem cScalarI_sound (terms : ℕ) {s y : ℚ} {payload : ScalarPayload}
    (hcheck : scalarCheck s y payload = true) :
    (cScalarI terms s y payload).Contains
      (cPrimitive (s : ℝ) (y : ℝ)) := by
  by_cases hy0 : y = 0
  · subst y
    simpa [cScalarI, cPrimitive] using
      RationalEnclosure.contains_point (0 : ℚ)
  · have hchecks := scalarCheck_parts_of_ne hy0 hcheck
    have hs := constAD_sound s
    have hy := constAD_sound y
    have homega := payload.omegaY.sound terms hchecks.1 hs hy
    have hw := payload.omegaZero.sound terms hchecks.2 hs
    have hresult := RationalEnclosure.contains_sub homega.1 hw.1
    simpa [cScalarI, hy0, cPrimitive] using hresult

end LRUpperKHistoricalACValues
end CourtadeKumar
