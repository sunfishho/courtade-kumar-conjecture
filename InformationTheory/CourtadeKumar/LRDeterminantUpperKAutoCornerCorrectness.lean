import InformationTheory.CourtadeKumar.LRDeterminantUpperKAutoSharpCorrectness

/-!
# Correctness of deterministic upper-K corner payloads

The four monotone endpoint pairs are generated from scalar omega payloads.
Their shallow success predicates imply the original explicit-corner checker.
-/

namespace CourtadeKumar

namespace LRUpperKHistoricalACValues.ScalarPayload

def autoSucceeds (sqrtFuel logFuel : ℕ) (s y : ℚ) : Bool :=
  if y = 0 then true
  else LROmegaADCertificate.autoSucceeds sqrtFuel logFuel
      (constAD s) (constAD y) &&
    LROmegaZeroADCertificate.autoSucceeds sqrtFuel logFuel (constAD s)

theorem auto_scalarCheck_of_succeeds (sqrtFuel logFuel : ℕ) (s y : ℚ)
    (hsucceeds : autoSucceeds sqrtFuel logFuel s y = true) :
    LRUpperKHistoricalACValues.scalarCheck s y
      (auto sqrtFuel logFuel s y) = true := by
  by_cases hy : y = 0
  · simp [LRUpperKHistoricalACValues.scalarCheck, hy]
  · have hparts :
        LROmegaADCertificate.autoSucceeds sqrtFuel logFuel
            (constAD s) (constAD y) = true ∧
        LROmegaZeroADCertificate.autoSucceeds sqrtFuel logFuel
            (constAD s) = true := by
      simpa [autoSucceeds, hy] using hsucceeds
    have homegaY := LROmegaADCertificate.auto_check_of_succeeds
      sqrtFuel logFuel (constAD s) (constAD y) hparts.1
    have homegaZero := LROmegaZeroADCertificate.auto_check_of_succeeds
      sqrtFuel logFuel (constAD s) hparts.2
    simp [LRUpperKHistoricalACValues.scalarCheck,
      LRUpperKHistoricalACValues.ScalarPayload.auto, hy,
      homegaY, homegaZero]

end LRUpperKHistoricalACValues.ScalarPayload

namespace LRUpperKExplicitCornerPayload

open LRUpperKReplayCertificate
open LRUpperKHistoricalACValues

def aPairAuto (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (input : RationalEnclosure) : Pair :=
  { lower := ScalarPayload.auto sqrtFuel logFuel box.sHi input.lower
    upper := ScalarPayload.auto sqrtFuel logFuel box.sLo input.upper }

def cPairAuto (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (input : RationalEnclosure) : Pair :=
  { lower := ScalarPayload.auto sqrtFuel logFuel box.sHi input.upper
    upper := ScalarPayload.auto sqrtFuel logFuel box.sLo input.lower }

def aPairAutoSucceeds (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (input : RationalEnclosure) : Bool :=
  ScalarPayload.autoSucceeds sqrtFuel logFuel box.sHi input.lower &&
    ScalarPayload.autoSucceeds sqrtFuel logFuel box.sLo input.upper

def cPairAutoSucceeds (sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (input : RationalEnclosure) : Bool :=
  ScalarPayload.autoSucceeds sqrtFuel logFuel box.sHi input.upper &&
    ScalarPayload.autoSucceeds sqrtFuel logFuel box.sLo input.lower

theorem aPairAuto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (input : RationalEnclosure)
    (hsucceeds : aPairAutoSucceeds sqrtFuel logFuel box input = true) :
    aCornerCheck box input (aPairAuto sqrtFuel logFuel box input) = true := by
  simp only [aPairAutoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [aCornerCheck, aPairAuto,
    ScalarPayload.auto_scalarCheck_of_succeeds _ _ _ _ hsucceeds.1,
    ScalarPayload.auto_scalarCheck_of_succeeds _ _ _ _ hsucceeds.2]

theorem cPairAuto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (input : RationalEnclosure)
    (hsucceeds : cPairAutoSucceeds sqrtFuel logFuel box input = true) :
    cCornerCheck box input (cPairAuto sqrtFuel logFuel box input) = true := by
  simp only [cPairAutoSucceeds, Bool.and_eq_true] at hsucceeds
  simp [cCornerCheck, cPairAuto,
    ScalarPayload.auto_scalarCheck_of_succeeds _ _ _ _ hsucceeds.1,
    ScalarPayload.auto_scalarCheck_of_succeeds _ _ _ _ hsucceeds.2]

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  let y0 := (y0AD box).value
  let e := (eAD box).value
  { aY0 := aPairAuto sqrtFuel logFuel box y0
    cY0 := cPairAuto sqrtFuel logFuel box y0
    aE := aPairAuto sqrtFuel logFuel box e
    cE := cPairAuto sqrtFuel logFuel box e }

def autoSucceeds (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Bool :=
  all4
    (aPairAutoSucceeds sqrtFuel logFuel box (y0AD box).value)
    (cPairAutoSucceeds sqrtFuel logFuel box (y0AD box).value)
    (aPairAutoSucceeds sqrtFuel logFuel box (eAD box).value)
    (cPairAutoSucceeds sqrtFuel logFuel box (eAD box).value)

theorem auto_check_of_succeeds (sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (hsucceeds : autoSucceeds sqrtFuel logFuel box = true) :
    check box (auto sqrtFuel logFuel box) = true := by
  have hparts :
      (aPairAutoSucceeds sqrtFuel logFuel box (y0AD box).value = true ∧
        cPairAutoSucceeds sqrtFuel logFuel box (y0AD box).value = true) ∧
      (aPairAutoSucceeds sqrtFuel logFuel box (eAD box).value = true ∧
        cPairAutoSucceeds sqrtFuel logFuel box (eAD box).value = true) := by
    simpa [autoSucceeds, all4] using hsucceeds
  have haY0 := aPairAuto_check_of_succeeds
    sqrtFuel logFuel box (y0AD box).value hparts.1.1
  have hcY0 := cPairAuto_check_of_succeeds
    sqrtFuel logFuel box (y0AD box).value hparts.1.2
  have haE := aPairAuto_check_of_succeeds
    sqrtFuel logFuel box (eAD box).value hparts.2.1
  have hcE := cPairAuto_check_of_succeeds
    sqrtFuel logFuel box (eAD box).value hparts.2.2
  simp [check, auto, all4, haY0, hcY0, haE, hcE]

end LRUpperKExplicitCornerPayload
end CourtadeKumar
