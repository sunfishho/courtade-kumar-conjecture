import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalPackedCertificate

namespace CourtadeKumar
namespace LRUpperKBalancedAuxiliaryChecker

open LRUpperKHistoricalACAD
open LRUpperKReplayCertificate

structure Inputs where
  s : RationalEnclosure
  e : RationalEnclosure
  y : RationalEnclosure
  b : RationalEnclosure

def endpointFlat (terms : ℕ) (y : ℚ)
    (prime : LRQPointCertificate)
    (sqrt : RationalEnclosure.SqrtCertificate) : Bool :=
  (prime.primeCheck y &&
    sqrt.check (RationalEnclosure.point y)) &&
  decide ((0 : ℚ) ≤ (prime.primeEnclosure terms).lower)

def scaleFlat (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQRegularizedScaleCertificate) : Bool :=
  decide (0 ≤ input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) &&
    if input.upper = 0 then true
    else endpointFlat terms input.upper certificate.upper certificate.sqrtUpper &&
      if input.lower = 0 then true
      else endpointFlat terms input.lower certificate.lower certificate.sqrtLower

def check (terms : ℕ) (input : Inputs)
    (payload : LRUpperKHistoricalACAD.Payload) : Bool :=
  (scaleFlat terms input.y (qY0ScaleCertificate payload) &&
    payload.sqrtE.check input.e) &&
  (payload.base.omegaZero.qPrimeAtS.value.check input.s &&
    payload.base.omegaY0.qPrimeAtB.check input.b)

theorem endpointFlat_eq_true_iff
    (terms : ℕ) (y : ℚ) (prime : LRQPointCertificate)
    (sqrt : RationalEnclosure.SqrtCertificate) :
    endpointFlat terms y prime sqrt = true ↔
      LRQRegularizedScaleCertificate.endpointCheck terms y prime sqrt = true := by
  simp [endpointFlat, LRQRegularizedScaleCertificate.endpointCheck,
    and_assoc]

theorem scaleFlat_eq_true_iff
    (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQRegularizedScaleCertificate) :
    scaleFlat terms input certificate = true ↔
      certificate.check terms input = true := by
  simp [scaleFlat, LRQRegularizedScaleCertificate.check,
    endpointFlat_eq_true_iff, and_assoc]

theorem auxiliaryCheck_of_checked
    {terms : ℕ} {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload} {input : Inputs}
    (hs : (sAD box).value = input.s)
    (he : (eAD box).value = input.e)
    (hy : (y0AD box).value = input.y)
    (hb : (y0BAd box).value = input.b)
    (hcheck : check terms input payload = true) :
    LRUpperKHistoricalACAD.auxiliaryCheck terms box payload = true := by
  simpa [check, LRUpperKHistoricalACAD.auxiliaryCheck,
    scaleFlat_eq_true_iff, hs, he, hy, hb, and_assoc] using hcheck

end LRUpperKBalancedAuxiliaryChecker
end CourtadeKumar
