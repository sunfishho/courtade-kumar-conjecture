import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalPackedCertificate

namespace CourtadeKumar
namespace LRUpperKBalancedBasePayloadChecker

open LRUpperKReplayCertificate

def all4 (a b c d : Bool) : Bool :=
  (a && b) && (c && d)

def check (box : CertificateBox)
    (payload : LRUpperKReplayCertificate.Payload) : Bool :=
  (all4
      (decide ((0 : ℚ) < (sAD box).value.lower))
      (decide ((0 : ℚ) < (ratioAD box).value.lower))
      (decide ((0 : ℚ) ≤ (hAD box).value.lower))
      (decide ((0 : ℚ) < (xAD box).value.lower)) &&
    all4
      (IntervalAD.sqrtCheck (vRadicandAD box).value payload.vSqrt)
      (decide ((0 : ℚ) < (vAD box payload).value.lower))
      (payload.omegaZero.check (sAD box))
      (payload.omegaY0.check (sAD box) (y0AD box))) &&
  (all4
      (payload.omegaE.check (sAD box) (eAD box))
      (payload.g0.check (vAD box payload))
      (payload.qY0.check (y0AD box).value)
      (payload.qE.check (eAD box).value) &&
    all4
      (payload.logOnePlusV.check (onePlusVI box payload))
      (payload.logBE.check (beAD box).value)
      (payload.logMeanY.check (meanYI box))
      (decide ((0 : ℚ) < (eAD box).value.lower))) &&
  decide ((0 : ℚ) < (threeYPlusOneI box).lower)

theorem payloadCheck_of_checked
    {box : CertificateBox}
    {payload : LRUpperKReplayCertificate.Payload}
    (hcheck : check box payload = true) :
    LRUpperKReplayCertificate.payloadCheck box payload = true := by
  simp only [check, all4, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  simp only [LRUpperKReplayCertificate.payloadCheck, decide_eq_true_eq]
  aesop

theorem valid_of_checked
    {box : CertificateBox}
    {payload : LRUpperKReplayCertificate.Payload}
    (hcheck : check box payload = true) :
    LRUpperKReplayCertificate.Valid box payload :=
  LRUpperKReplayCertificate.payloadCheck_sound
    (payloadCheck_of_checked hcheck)

end LRUpperKBalancedBasePayloadChecker
end CourtadeKumar
