import InformationTheory.CourtadeKumar.LRDeterminantAutoCompositeCertificateCorrectness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKBalancedBasePayloadChecker

/-!
# Correctness of the deterministic upper-K base payload

The executable success predicate below follows the shallow domain checks of
the automatically generated base payload.  Its proof reconstructs the
original checked payload without evaluating the deeply nested checker at once.
-/

namespace CourtadeKumar
namespace LRUpperKReplayCertificate

structure AutoValid (sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Prop where
  sPositive : (0 : ℚ) < (sAD box).value.lower
  ratioPositive : (0 : ℚ) < (ratioAD box).value.lower
  hNonnegative : (0 : ℚ) ≤ (hAD box).value.lower
  xPositive : (0 : ℚ) < (xAD box).value.lower
  vRadicandNonnegative : (0 : ℚ) ≤ (vRadicandAD box).value.lower
  vRadicandOrdered :
    (vRadicandAD box).value.lower ≤ (vRadicandAD box).value.upper
  vRootPositive : (0 : ℚ) < (auto sqrtFuel logFuel box).vSqrt.lower
  vPositive : (0 : ℚ) < (vAD box (auto sqrtFuel logFuel box)).value.lower
  omegaZero : LROmegaZeroADCertificate.autoSucceeds sqrtFuel logFuel
    (sAD box) = true
  omegaY0 : LROmegaZeroIntervalCertificate.autoSucceeds
    (sqrtFuel + 8) (logFuel + 8) (sAD box) (y0AD box) = true
  omegaE : LROmegaADCertificate.autoSucceeds sqrtFuel logFuel
    (sAD box) (eAD box) = true
  g0 : LRG0ADCertificate.autoSucceeds logFuel
    (vAD box (auto sqrtFuel logFuel box)) = true
  qY0 : LRQZeroIntervalCertificate.autoSucceeds (y0AD box).value = true
  qE : LRQIntervalCertificate.autoSucceeds sqrtFuel logFuel
    (eAD box).value = true
  logOnePlusV :
    RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
      (onePlusVI box (auto sqrtFuel logFuel box)) = true
  logBE : RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
    (beAD box).value = true
  logMeanY : RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
    (meanYI box) = true
  ePositive : (0 : ℚ) < (eAD box).value.lower
  threeYPlusOnePositive : (0 : ℚ) < (threeYPlusOneI box).lower

def autoSucceeds (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Bool :=
  decide ((0 : ℚ) < (sAD box).value.lower) &&
  decide ((0 : ℚ) < (ratioAD box).value.lower) &&
  decide ((0 : ℚ) ≤ (hAD box).value.lower) &&
  decide ((0 : ℚ) < (xAD box).value.lower) &&
  decide ((0 : ℚ) ≤ (vRadicandAD box).value.lower) &&
  decide ((vRadicandAD box).value.lower ≤
    (vRadicandAD box).value.upper) &&
  decide ((0 : ℚ) < (auto sqrtFuel logFuel box).vSqrt.lower) &&
  decide ((0 : ℚ) < (vAD box (auto sqrtFuel logFuel box)).value.lower) &&
  LROmegaZeroADCertificate.autoSucceeds sqrtFuel logFuel (sAD box) &&
  LROmegaZeroIntervalCertificate.autoSucceeds
    (sqrtFuel + 8) (logFuel + 8) (sAD box) (y0AD box) &&
  LROmegaADCertificate.autoSucceeds sqrtFuel logFuel
    (sAD box) (eAD box) &&
  LRG0ADCertificate.autoSucceeds logFuel
    (vAD box (auto sqrtFuel logFuel box)) &&
  LRQZeroIntervalCertificate.autoSucceeds (y0AD box).value &&
  LRQIntervalCertificate.autoSucceeds sqrtFuel logFuel (eAD box).value &&
  RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
    (onePlusVI box (auto sqrtFuel logFuel box)) &&
  RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
    (beAD box).value &&
  RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
    (meanYI box) &&
  decide ((0 : ℚ) < (eAD box).value.lower) &&
  decide ((0 : ℚ) < (threeYPlusOneI box).lower)

theorem autoValid_of_succeeds (sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (hsucceeds : autoSucceeds sqrtFuel logFuel box = true) :
    AutoValid sqrtFuel logFuel box := by
  simp only [autoSucceeds, Bool.and_eq_true] at hsucceeds
  rcases hsucceeds with ⟨hrest, hthree⟩
  rcases hrest with ⟨hrest, he⟩
  rcases hrest with ⟨hrest, hlogMeanY⟩
  rcases hrest with ⟨hrest, hlogBE⟩
  rcases hrest with ⟨hrest, hlogOnePlusV⟩
  rcases hrest with ⟨hrest, hqE⟩
  rcases hrest with ⟨hrest, hqY0⟩
  rcases hrest with ⟨hrest, hg0⟩
  rcases hrest with ⟨hrest, homegaE⟩
  rcases hrest with ⟨hrest, homegaY0⟩
  rcases hrest with ⟨hrest, homegaZero⟩
  rcases hrest with ⟨hrest, hv⟩
  rcases hrest with ⟨hrest, hroot⟩
  rcases hrest with ⟨hrest, hradOrder⟩
  rcases hrest with ⟨hrest, hrad0⟩
  rcases hrest with ⟨hrest, hx⟩
  rcases hrest with ⟨hrest, hh⟩
  rcases hrest with ⟨hs, hratio⟩
  exact
    { sPositive := by simpa using hs
      ratioPositive := by simpa using hratio
      hNonnegative := by simpa using hh
      xPositive := by simpa using hx
      vRadicandNonnegative := by simpa using hrad0
      vRadicandOrdered := by simpa using hradOrder
      vRootPositive := by simpa using hroot
      vPositive := by simpa using hv
      omegaZero := homegaZero
      omegaY0 := homegaY0
      omegaE := homegaE
      g0 := hg0
      qY0 := hqY0
      qE := hqE
      logOnePlusV := hlogOnePlusV
      logBE := hlogBE
      logMeanY := hlogMeanY
      ePositive := by simpa using he
      threeYPlusOnePositive := by simpa using hthree }

theorem auto_payloadCheck_of_succeeds (sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (hsucceeds : autoSucceeds sqrtFuel logFuel box = true) :
    payloadCheck box (auto sqrtFuel logFuel box) = true := by
  let payload := auto sqrtFuel logFuel box
  have hvalid := autoValid_of_succeeds sqrtFuel logFuel box hsucceeds
  have hvSqrtCertificate :
      payload.vSqrt.check (vRadicandAD box).value = true := by
    change (RationalEnclosure.autoSqrtCertificate sqrtFuel
      (vRadicandAD box).value).check (vRadicandAD box).value = true
    exact RationalEnclosure.autoSqrtCertificate_check
      hvalid.vRadicandNonnegative hvalid.vRadicandOrdered sqrtFuel
  have hvSqrt :
      IntervalAD.sqrtCheck (vRadicandAD box).value payload.vSqrt = true := by
    simp [IntervalAD.sqrtCheck, hvSqrtCertificate, hvalid.vRootPositive,
      payload]
  have homegaZero : payload.omegaZero.check (sAD box) = true := by
    change (LROmegaZeroADCertificate.auto sqrtFuel logFuel
      (sAD box)).check (sAD box) = true
    exact LROmegaZeroADCertificate.auto_check_of_succeeds
      sqrtFuel logFuel (sAD box) hvalid.omegaZero
  have homegaY0 : payload.omegaY0.check (sAD box) (y0AD box) = true := by
    change (LROmegaZeroIntervalCertificate.auto
      (sqrtFuel + 8) (logFuel + 8) (sAD box) (y0AD box)).check
        (sAD box) (y0AD box) = true
    exact LROmegaZeroIntervalCertificate.auto_check_of_succeeds
      (sqrtFuel + 8) (logFuel + 8) (sAD box) (y0AD box) hvalid.omegaY0
  have homegaE : payload.omegaE.check (sAD box) (eAD box) = true := by
    change (LROmegaADCertificate.auto sqrtFuel logFuel
      (sAD box) (eAD box)).check (sAD box) (eAD box) = true
    exact LROmegaADCertificate.auto_check_of_succeeds
      sqrtFuel logFuel (sAD box) (eAD box) hvalid.omegaE
  have hg0 : payload.g0.check (vAD box payload) = true := by
    change (LRG0ADCertificate.auto logFuel (vAD box payload)).check
      (vAD box payload) = true
    exact LRG0ADCertificate.auto_check_of_succeeds
      logFuel (vAD box payload) (by simpa [payload] using hvalid.g0)
  have hqY0 : payload.qY0.check (y0AD box).value = true := by
    change (LRQZeroIntervalCertificate.auto
      (sqrtFuel + 8) (logFuel + 8) (y0AD box).value).check
        (y0AD box).value = true
    exact LRQZeroIntervalCertificate.auto_check_of_succeeds
      (sqrtFuel + 8) (logFuel + 8) (y0AD box).value hvalid.qY0
  have hqE : payload.qE.check (eAD box).value = true := by
    change (LRQIntervalCertificate.auto sqrtFuel logFuel
      (eAD box).value).check (eAD box).value = true
    exact LRQIntervalCertificate.auto_check_of_succeeds
      sqrtFuel logFuel (eAD box).value hvalid.qE
  have hlogOnePlusV : payload.logOnePlusV.check
      (onePlusVI box payload) = true := by
    change (RationalEnclosure.autoLogIntervalCertificate logFuel
      (onePlusVI box payload)).check (onePlusVI box payload) = true
    exact RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (onePlusVI box payload) (by
        simpa [payload] using hvalid.logOnePlusV)
  have hlogBE : payload.logBE.check (beAD box).value = true := by
    change (RationalEnclosure.autoLogIntervalCertificate logFuel
      (beAD box).value).check (beAD box).value = true
    exact RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (beAD box).value hvalid.logBE
  have hlogMean : payload.logMeanY.check (meanYI box) = true := by
    change (RationalEnclosure.autoLogIntervalCertificate logFuel
      (meanYI box)).check (meanYI box) = true
    exact RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (meanYI box) hvalid.logMeanY
  simp only [payloadCheck, decide_eq_true_eq]
  exact ⟨hvalid.sPositive, hvalid.ratioPositive, hvalid.hNonnegative,
    hvalid.xPositive, hvSqrt, hvalid.vPositive, homegaZero, homegaY0,
    homegaE, hg0, hqY0, hqE, hlogOnePlusV, hlogBE, hlogMean,
    hvalid.ePositive, hvalid.threeYPlusOnePositive⟩

end LRUpperKReplayCertificate
end CourtadeKumar
