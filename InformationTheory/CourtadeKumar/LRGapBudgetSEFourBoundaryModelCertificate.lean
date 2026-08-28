import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryAnalytic
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Rational interval certificate for the cancellation-safe boundary model

This evaluator contains exactly the elementary expression `lowerModel` from
`LRGapBudgetSEFourBoundaryAnalytic`.  All transcendental nodes are accompanied
by ordinary kernel-checked square-root or logarithm certificates.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEFourBoundaryModelCertificate

open LRGapBudgetSEFourBoundaryAnalytic

def xI (sI chiI : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1)
    (RationalEnclosure.mul (RationalEnclosure.point 4)
      (RationalEnclosure.mul chiI sI))

def radicandI (sI chiI : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.sub (RationalEnclosure.point 1)
      (RationalEnclosure.mul (RationalEnclosure.point 4) sI))
    (xI sI chiI)

def leftCoeffI (sI chiI : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1)
    (RationalEnclosure.mul (RationalEnclosure.point 4)
      (RationalEnclosure.mul chiI
        (RationalEnclosure.sub (RationalEnclosure.point 1) sI)))

def rightCoeffI (sI : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 5)
    (RationalEnclosure.mul (RationalEnclosure.point 4) sI)

structure Payload where
  vSqrt : RationalEnclosure.SqrtCertificate
  logTwo : RationalEnclosure.LogIntervalCertificate
  logForty : RationalEnclosure.LogIntervalCertificate
  logLeft : RationalEnclosure.LogIntervalCertificate
  logRight : RationalEnclosure.LogIntervalCertificate
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate

def vI (payload : Payload) : RationalEnclosure := payload.vSqrt.enclosure

def onePlusVI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) (vI payload)

def twoPlusVI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 2) (vI payload)

def slopeCoeffI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.mul (RationalEnclosure.point 2) (twoPlusVI payload))
    (onePlusVI payload)

def coreCoeffI (sI chiI : RationalEnclosure)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add (leftCoeffI sI chiI)
      (RationalEnclosure.div (rightCoeffI sI) (vI payload)))
    (slopeCoeffI payload)

/-- Exact rational interval transcription of `lowerModel`. -/
def evaluate (terms : ℕ) (sI chiI : RationalEnclosure)
    (payload : Payload) : RationalEnclosure :=
  let one := RationalEnclosure.point 1
  let two := RationalEnclosure.point 2
  let four := RationalEnclosure.point 4
  let fifteen := RationalEnclosure.point 15
  let thirtyTwo := RationalEnclosure.point 32
  let x := xI sI chiI
  let v := vI payload
  let onePlusV := onePlusVI payload
  let left := leftCoeffI sI chiI
  let right := rightCoeffI sI
  let slope := slopeCoeffI payload
  let core := coreCoeffI sI chiI payload
  let logTwo := payload.logTwo.enclosure terms
  let log40 := payload.logForty.enclosure terms
  let logLeft := payload.logLeft.enclosure terms
  let logRight := payload.logRight.enclosure terms
  let logOnePlusV := payload.logOnePlusV.enclosure terms
  let logTwoPlusV := payload.logTwoPlusV.enclosure terms
  let logFactor := RationalEnclosure.sub
    (RationalEnclosure.add logTwo logOnePlusV) logTwoPlusV
  let oneMinusS := RationalEnclosure.sub one sI
  let oneMinusChi := RationalEnclosure.sub one chiI
  let shapeNumerator := RationalEnclosure.mul thirtyTwo
    (RationalEnclosure.mul oneMinusS
      (RationalEnclosure.mul sI
        (RationalEnclosure.mul oneMinusChi oneMinusChi)))
  let shapePayment := RationalEnclosure.neg
    (RationalEnclosure.div
      (RationalEnclosure.div
        (RationalEnclosure.div
          (RationalEnclosure.div shapeNumerator x) x) onePlusV) onePlusV)
  let ratio := RationalEnclosure.div onePlusV v
  let slopePayment := RationalEnclosure.mul ratio
    (RationalEnclosure.add logTwo
      (RationalEnclosure.mul two logFactor))
  let qBracket := RationalEnclosure.add
    (RationalEnclosure.sub
      (RationalEnclosure.sub
        (RationalEnclosure.mul core
          (RationalEnclosure.add log40 one))
        (RationalEnclosure.mul left logLeft))
      (RationalEnclosure.mul
        (RationalEnclosure.div right v) logRight))
    (RationalEnclosure.mul
      (RationalEnclosure.mul four slope) logTwo)
  let qPayment := RationalEnclosure.div qBracket four
  let remainderPayment := RationalEnclosure.div
    (RationalEnclosure.mul two log40) fifteen
  RationalEnclosure.sub
    (RationalEnclosure.add
      (RationalEnclosure.sub shapePayment slopePayment) qPayment)
    remainderPayment

def check (sI chiI : RationalEnclosure) (payload : Payload) : Bool :=
  decide ((0 : ℚ) < (xI sI chiI).lower ∧
      (0 : ℚ) < (radicandI sI chiI).lower) &&
    payload.vSqrt.check (radicandI sI chiI) &&
    payload.logTwo.check (RationalEnclosure.point 2) &&
    payload.logForty.check (RationalEnclosure.point 40) &&
    payload.logLeft.check (leftCoeffI sI chiI) &&
    payload.logRight.check (rightCoeffI sI) &&
    payload.logOnePlusV.check (onePlusVI payload) &&
    payload.logTwoPlusV.check (twoPlusVI payload) &&
    decide ((0 : ℚ) < (vI payload).lower ∧
      (0 : ℚ) < (onePlusVI payload).lower ∧
      (0 : ℚ) < (twoPlusVI payload).lower)

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4000 in
theorem evaluate_sound (terms : ℕ) {sI chiI : RationalEnclosure}
    {s chi : ℝ} {payload : Payload}
    (hs : sI.Contains s) (hchi : chiI.Contains chi)
    (hcheck : check sI chiI payload = true) :
    (evaluate terms sI chiI payload).Contains (lowerModel s chi) := by
  have hparts :
      ((0 : ℚ) < (xI sI chiI).lower ∧
        (0 : ℚ) < (radicandI sI chiI).lower) ∧
      payload.vSqrt.check (radicandI sI chiI) = true ∧
      payload.logTwo.check (RationalEnclosure.point 2) = true ∧
      payload.logForty.check (RationalEnclosure.point 40) = true ∧
      payload.logLeft.check (leftCoeffI sI chiI) = true ∧
      payload.logRight.check (rightCoeffI sI) = true ∧
      payload.logOnePlusV.check (onePlusVI payload) = true ∧
      payload.logTwoPlusV.check (twoPlusVI payload) = true ∧
      ((0 : ℚ) < (vI payload).lower ∧
        (0 : ℚ) < (onePlusVI payload).lower ∧
        (0 : ℚ) < (twoPlusVI payload).lower) := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck
  have hvLower : (0 : ℚ) < (vI payload).lower :=
    hparts.2.2.2.2.2.2.2.2.1
  have honePlusLower : (0 : ℚ) < (onePlusVI payload).lower :=
    hparts.2.2.2.2.2.2.2.2.2.1
  have htwoPlusLower : (0 : ℚ) < (twoPlusVI payload).lower :=
    hparts.2.2.2.2.2.2.2.2.2.2
  have hone := RationalEnclosure.contains_point 1
  have htwo := RationalEnclosure.contains_point 2
  have hfour := RationalEnclosure.contains_point 4
  have hfifteen := RationalEnclosure.contains_point 15
  have hthirtyTwo := RationalEnclosure.contains_point 32
  have hchiS := RationalEnclosure.contains_mul hchi hs
  have hxRaw := RationalEnclosure.contains_sub hone
    (RationalEnclosure.contains_mul hfour hchiS)
  have hx : (xI sI chiI).Contains (x s chi) := by
    unfold xI x
    convert hxRaw using 1 <;> ring
  have hxLowerReal : (0 : ℝ) < (xI sI chiI).lower := by
    exact_mod_cast hparts.1.1
  have hxPos : 0 < x s chi := hxLowerReal.trans_le hx.1
  have hnum := RationalEnclosure.contains_sub hone
    (RationalEnclosure.contains_mul hfour hs)
  have hrad := RationalEnclosure.contains_div hparts.1.1 hnum hx
  have hvRaw := payload.vSqrt.sound hparts.2.1 hrad
  have hv : (vI payload).Contains (v s chi) := by
    simpa [vI, v] using hvRaw
  have hvLowerReal : (0 : ℝ) < (vI payload).lower := by
    exact_mod_cast hvLower
  have hvPos : 0 < v s chi := hvLowerReal.trans_le hv.1
  have honePlusVPos : 0 < 1 + v s chi := by linarith
  have honeMinusS := RationalEnclosure.contains_sub hone hs
  have honeMinusChi := RationalEnclosure.contains_sub hone hchi
  have hleftRaw := RationalEnclosure.contains_add hone
    (RationalEnclosure.contains_mul hfour
      (RationalEnclosure.contains_mul hchi honeMinusS))
  have hleft : (leftCoeffI sI chiI).Contains (leftCoeff s chi) := by
    unfold leftCoeffI leftCoeff
    convert hleftRaw using 1 <;> ring
  have hrightRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 5)
    (RationalEnclosure.contains_mul hfour hs)
  have hright : (rightCoeffI sI).Contains (rightCoeff s) := by
    simpa [rightCoeffI, rightCoeff] using hrightRaw
  have honePlusV := RationalEnclosure.contains_add hone hv
  have htwoPlusV := RationalEnclosure.contains_add htwo hv
  have hslopeRaw := RationalEnclosure.contains_div honePlusLower
    (RationalEnclosure.contains_mul htwo htwoPlusV) honePlusV
  have hslope : (slopeCoeffI payload).Contains (slopeCoeff s chi) := by
    simpa [slopeCoeffI, slopeCoeff] using hslopeRaw
  have hrightDiv := RationalEnclosure.contains_div
    hvLower hright hv
  have hcoreRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hleft hrightDiv) hslope
  have hcore : (coreCoeffI sI chiI payload).Contains (coreCoeff s chi) := by
    simpa [coreCoeffI, coreCoeff] using hcoreRaw
  have hlogTwo := payload.logTwo.sound terms hparts.2.2.1
    (RationalEnclosure.contains_point 2)
  have hlog40 := payload.logForty.sound terms hparts.2.2.2.1
    (RationalEnclosure.contains_point 40)
  have hlogLeft := payload.logLeft.sound terms hparts.2.2.2.2.1 hleft
  have hlogRight := payload.logRight.sound terms hparts.2.2.2.2.2.1 hright
  have hlogOnePlus := payload.logOnePlusV.sound terms
    hparts.2.2.2.2.2.2.1 honePlusV
  have hlogTwoPlus := payload.logTwoPlusV.sound terms
    hparts.2.2.2.2.2.2.2.1 htwoPlusV
  have hlogFactor := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hlogTwo hlogOnePlus) hlogTwoPlus
  have hshapeNumerator := RationalEnclosure.contains_mul hthirtyTwo
    (RationalEnclosure.contains_mul honeMinusS
      (RationalEnclosure.contains_mul hs
        (RationalEnclosure.contains_mul honeMinusChi honeMinusChi)))
  have hshapePayment := RationalEnclosure.contains_neg
    (RationalEnclosure.contains_div
      honePlusLower
      (RationalEnclosure.contains_div honePlusLower
        (RationalEnclosure.contains_div hparts.1.1
          (RationalEnclosure.contains_div hparts.1.1 hshapeNumerator hx) hx)
        honePlusV)
      honePlusV)
  have hratio := RationalEnclosure.contains_div
    hvLower honePlusV hv
  have hslopePayment := RationalEnclosure.contains_mul hratio
    (RationalEnclosure.contains_add hlogTwo
      (RationalEnclosure.contains_mul htwo hlogFactor))
  have hqBracket := RationalEnclosure.contains_add
    (RationalEnclosure.contains_sub
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_mul hcore
          (RationalEnclosure.contains_add hlog40 hone))
        (RationalEnclosure.contains_mul hleft hlogLeft))
      (RationalEnclosure.contains_mul hrightDiv hlogRight))
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_mul hfour hslope) hlogTwo)
  have hqPayment := RationalEnclosure.contains_div
    (by norm_num : (0 : ℚ) < 4) hqBracket hfour
  have hremainder := RationalEnclosure.contains_div
    (by norm_num : (0 : ℚ) < 15)
    (RationalEnclosure.contains_mul htwo hlog40) hfifteen
  have htotal := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_sub hshapePayment hslopePayment) hqPayment)
    hremainder
  unfold evaluate lowerModel logFactor
  dsimp only
  convert htotal using 1 <;>
    field_simp [hxPos.ne', hvPos.ne', honePlusVPos.ne'] <;> ring_nf

def nonnegative (terms : ℕ) (sI chiI : RationalEnclosure)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) ≤ (evaluate terms sI chiI payload).lower)

theorem nonnegative_sound (terms : ℕ) {sI chiI : RationalEnclosure}
    {s chi : ℝ} {payload : Payload}
    (hs : sI.Contains s) (hchi : chiI.Contains chi)
    (hcheck : check sI chiI payload = true)
    (hnonnegative : nonnegative terms sI chiI payload = true) :
    0 ≤ lowerModel s chi := by
  have hsound := evaluate_sound terms hs hchi hcheck
  have hlower : (0 : ℝ) ≤ (evaluate terms sI chiI payload).lower := by
    exact_mod_cast (show (0 : ℚ) ≤ (evaluate terms sI chiI payload).lower by
      simpa [nonnegative] using hnonnegative)
  exact hlower.trans hsound.1

def auto (sqrtFuel logFuel : ℕ) (sI chiI : RationalEnclosure) : Payload :=
  let vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
    (radicandI sI chiI)
  let v := vSqrt.enclosure
  let onePlusV := RationalEnclosure.add (RationalEnclosure.point 1) v
  let twoPlusV := RationalEnclosure.add (RationalEnclosure.point 2) v
  { vSqrt := vSqrt
    logTwo := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.point 2)
    logForty := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.point 40)
    logLeft := RationalEnclosure.autoLogIntervalCertificate logFuel
      (leftCoeffI sI chiI)
    logRight := RationalEnclosure.autoLogIntervalCertificate logFuel
      (rightCoeffI sI)
    logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel onePlusV
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel twoPlusV }

def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (sI chiI : RationalEnclosure) : Bool :=
  let payload := auto sqrtFuel logFuel sI chiI
  check sI chiI payload && nonnegative terms sI chiI payload

theorem autoAccepts_sound (terms sqrtFuel logFuel : ℕ)
    (sI chiI : RationalEnclosure)
    (haccept : autoAccepts terms sqrtFuel logFuel sI chiI = true) :
    ∀ s chi, sI.Contains s → chiI.Contains chi → 0 ≤ lowerModel s chi := by
  intro s chi hs hchi
  have hparts : check sI chiI (auto sqrtFuel logFuel sI chiI) = true ∧
      nonnegative terms sI chiI (auto sqrtFuel logFuel sI chiI) = true := by
    simpa [autoAccepts] using haccept
  exact nonnegative_sound terms hs hchi hparts.1 hparts.2

end LRGapBudgetSEFourBoundaryModelCertificate
end CourtadeKumar
