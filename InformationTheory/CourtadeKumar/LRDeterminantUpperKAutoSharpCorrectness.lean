import InformationTheory.CourtadeKumar.LRDeterminantUpperKAutoBaseCorrectness
import InformationTheory.CourtadeKumar.LRDeterminantAutoRegularizedScaleCorrectness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKRoundedExplicitCornerEvaluator

/-!
# Correctness of the deterministic upper-K sharp payload

The complete historical analytic payload is reconstructed from the verified
base payload, regularized scale certificate, and square-root certificate.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalConcreteEvaluator

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD

def autoPayloadSucceeds (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  LRUpperKReplayCertificate.autoSucceeds sqrtFuel logFuel box &&
  LRQRegularizedScaleCertificate.autoSucceeds terms
    (sqrtFuel + 8) (logFuel + 8) (y0AD box).value &&
  decide ((0 : ℚ) ≤ (eAD box).value.lower) &&
  decide ((eAD box).value.lower ≤ (eAD box).value.upper)

theorem autoPayload_check_of_succeeds (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (hsucceeds : autoPayloadSucceeds terms sqrtFuel logFuel box = true) :
    LRUpperKHistoricalACAD.check terms box
      (autoPayload sqrtFuel logFuel box) = true := by
  simp only [autoPayloadSucceeds, Bool.and_eq_true] at hsucceeds
  rcases hsucceeds with ⟨hrest, heOrder⟩
  rcases hrest with ⟨hrest, heNonnegative⟩
  rcases hrest with ⟨hbaseSuccess, hscaleSuccess⟩
  have heNonnegative' : (0 : ℚ) ≤ (eAD box).value.lower := by
    simpa using heNonnegative
  have heOrder' : (eAD box).value.lower ≤ (eAD box).value.upper := by
    simpa using heOrder
  let base := LRUpperKReplayCertificate.auto sqrtFuel logFuel box
  let payload := autoPayload sqrtFuel logFuel box
  have hbase : LRUpperKReplayCertificate.payloadCheck box base = true :=
    LRUpperKReplayCertificate.auto_payloadCheck_of_succeeds
      sqrtFuel logFuel box hbaseSuccess
  have hbasePayload :
      LRUpperKReplayCertificate.payloadCheck box payload.base = true := by
    change LRUpperKReplayCertificate.payloadCheck box base = true
    exact hbase
  have hbaseValid := LRUpperKReplayCertificate.payloadCheck_sound hbase
  have hscale : (qY0ScaleCertificate payload).check terms
      (y0AD box).value = true := by
    change (LRQRegularizedScaleCertificate.auto
      (sqrtFuel + 8) (logFuel + 8) (y0AD box).value).check terms
        (y0AD box).value = true
    exact LRQRegularizedScaleCertificate.auto_check_of_succeeds
      terms (sqrtFuel + 8) (logFuel + 8) (y0AD box).value hscaleSuccess
  have hsqrtE : payload.sqrtE.check (eAD box).value = true := by
    change (RationalEnclosure.autoSqrtCertificate (sqrtFuel + 8)
      (eAD box).value).check (eAD box).value = true
    exact RationalEnclosure.autoSqrtCertificate_check
      heNonnegative' heOrder' (sqrtFuel + 8)
  have hprimeS : payload.base.omegaZero.qPrimeAtS.value.check
      (sAD box).value = true := by
    have hparts :
        payload.base.omegaZero.qAtS.check (sAD box).value = true ∧
        payload.base.omegaZero.qPrimeAtS.check (sAD box).value = true := by
      simpa [payload, base, LROmegaZeroADCertificate.check] using
        hbaseValid.omegaZeroCheck
    have hprimeParts :
        payload.base.omegaZero.qPrimeAtS.value.check (sAD box).value = true ∧
        lrQSecondCoarseCheck (sAD box).value = true := by
      simpa [LRQPrimeADCertificate.check] using hparts.2
    exact hprimeParts.1
  have hprimeB : payload.base.omegaY0.qPrimeAtB.check
      (y0BAd box).value = true := by
    have hparts :
        (payload.base.omegaY0.qAtB.check (y0BAd box).value = true ∧
          payload.base.omegaY0.qAtY.check (y0AD box).value = true) ∧
        payload.base.omegaY0.qPrimeAtB.check (y0BAd box).value = true := by
      simpa [payload, base, LROmegaZeroIntervalCertificate.check,
        y0BAd] using hbaseValid.omegaY0Check
    exact hparts.2
  have hauxiliary :
      LRUpperKHistoricalACAD.auxiliaryCheck terms box payload = true := by
    simp [LRUpperKHistoricalACAD.auxiliaryCheck, hscale, hsqrtE,
      hprimeS, hprimeB]
  simp only [LRUpperKHistoricalACAD.check, Bool.and_eq_true]
  exact ⟨hbasePayload, hauxiliary⟩

end LRUpperKHistoricalConcreteEvaluator
end CourtadeKumar
