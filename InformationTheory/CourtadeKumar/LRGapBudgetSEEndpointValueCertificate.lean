import InformationTheory.CourtadeKumar.LRGapBudgetSEEndpointCertificate
import InformationTheory.CourtadeKumar.LRGapBudgetSECertificate

/-!
# Closed-endpoint value certificate for the bounded gap budget

The ordinary interval-AD evaluator for `lrGapBudgetSEChi` contains `Q'`
nodes and therefore cannot cover boxes that touch `s = e = 0`.  The boundary
argument at `k = 4` only needs the value of the gap budget.  This evaluator
uses the zero-aware value enclosure for every `Q` node, so it remains valid
on the closed endpoint while retaining exact rational interval arithmetic.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEEndpointValueCertificate

def sI (box : CertificateBox) : RationalEnclosure := box.sInterval
def eI (box : CertificateBox) : RationalEnclosure := box.kInterval
def chiI (box : CertificateBox) : RationalEnclosure := box.chiInterval

def xI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.sub (RationalEnclosure.point 1)
    (RationalEnclosure.mul (chiI box) (eI box))

def radicandI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.sub (RationalEnclosure.point 1) (eI box))
    (xI box)

def by0I (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (sI box)
    (RationalEnclosure.mul
      (RationalEnclosure.sub (RationalEnclosure.point 1) (sI box))
      (RationalEnclosure.mul (chiI box) (eI box)))

def beI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add (sI box)
    (RationalEnclosure.mul
      (RationalEnclosure.sub (RationalEnclosure.point 1) (sI box))
      (eI box))

structure Payload where
  vSqrt : RationalEnclosure.SqrtCertificate
  g0 : LRG0ADCertificate
  qBY0 : LRQZeroIntervalCertificate
  qBE : LRQZeroIntervalCertificate
  qS : LRQZeroIntervalCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate

def vI (payload : Payload) : RationalEnclosure := payload.vSqrt.enclosure

def vAD (payload : Payload) : IntervalAD :=
  IntervalAD.parameter (vI payload)

def onePlusVI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) (vI payload)

def twoPlusVI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 2) (vI payload)

/-- Exact rational-interval transcription of `lrGapBudgetSEChi`. -/
def evaluate (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let one := RationalEnclosure.point 1
  let two := RationalEnclosure.point 2
  let s := sI box
  let v := vI payload
  let onePlusV := onePlusVI payload
  let twoPlusV := twoPlusVI payload
  let g0 := (payload.g0.evaluate terms (vAD payload)).value
  let qBY0 := payload.qBY0.enclosure terms (by0I box)
  let qBE := payload.qBE.enclosure terms (beI box)
  let qS := payload.qS.enclosure terms s
  let logTwo := payload.g0.logTwo.enclosure terms
  let logOnePlusV := payload.g0.logOnePlusV.enclosure terms
  let logTwoPlusV := payload.logTwoPlusV.enclosure terms
  let logFactor := RationalEnclosure.sub
    (RationalEnclosure.add logTwo logOnePlusV) logTwoPlusV
  let ratio := RationalEnclosure.div onePlusV v
  let delta := RationalEnclosure.sub qS (RationalEnclosure.mul s logTwo)
  let main := RationalEnclosure.add
    (RationalEnclosure.add
      (RationalEnclosure.mul (RationalEnclosure.sub one s) g0) qBY0)
    (RationalEnclosure.div qBE v)
  let slopeCost := RationalEnclosure.mul (RationalEnclosure.mul s ratio)
    (RationalEnclosure.add logTwo
      (RationalEnclosure.mul two logFactor))
  let deltaCost := RationalEnclosure.mul
    (RationalEnclosure.mul two
      (RationalEnclosure.div twoPlusV onePlusV)) delta
  RationalEnclosure.sub (RationalEnclosure.sub main slopeCost) deltaCost

def check (box : CertificateBox) (payload : Payload) : Bool :=
  decide ((0 : ℚ) < (xI box).lower ∧
      (0 : ℚ) < (radicandI box).lower) &&
    payload.vSqrt.check (radicandI box) &&
    payload.g0.check (vAD payload) &&
    payload.qBY0.check (by0I box) &&
    payload.qBE.check (beI box) &&
    payload.qS.check (sI box) &&
    payload.logTwoPlusV.check (twoPlusVI payload) &&
    decide ((0 : ℚ) < (vI payload).lower ∧
      (0 : ℚ) < (onePlusVI payload).lower ∧
      (0 : ℚ) < (twoPlusVI payload).lower)

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4000 in
theorem evaluate_sound (terms : ℕ) {box : CertificateBox}
    {s e chi : ℝ} {payload : Payload}
    (hs : (sI box).Contains s) (he : (eI box).Contains e)
    (hchi : (chiI box).Contains chi)
    (hcheck : check box payload = true) :
    (evaluate terms box payload).Contains (lrGapBudgetSEChi s e chi) := by
  have hparts :
      ((0 : ℚ) < (xI box).lower ∧
        (0 : ℚ) < (radicandI box).lower) ∧
      payload.vSqrt.check (radicandI box) = true ∧
      payload.g0.check (vAD payload) = true ∧
      payload.qBY0.check (by0I box) = true ∧
      payload.qBE.check (beI box) = true ∧
      payload.qS.check (sI box) = true ∧
      payload.logTwoPlusV.check (twoPlusVI payload) = true ∧
      ((0 : ℚ) < (vI payload).lower ∧
        (0 : ℚ) < (onePlusVI payload).lower ∧
        (0 : ℚ) < (twoPlusVI payload).lower) := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck
  have hchiE := RationalEnclosure.contains_mul hchi he
  have hxRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hchiE
  set x : ℝ := 1 - chi * e with hxDef
  have hx : (xI box).Contains x := by
    rw [hxDef]
    simpa [xI] using hxRaw
  have hnum := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) he
  have hrad := RationalEnclosure.contains_div hparts.1.1 hnum hx
  set v : ℝ := Real.sqrt ((1 - e) / x) with hvDef
  have hvRaw := payload.vSqrt.sound hparts.2.1 hrad
  have hv : (vI payload).Contains v := by
    rw [hvDef]
    simpa [vI] using hvRaw
  have honeMinusS := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hs
  have hby0Raw := RationalEnclosure.contains_add hs
    (RationalEnclosure.contains_mul honeMinusS hchiE)
  have hby0 : (by0I box).Contains (lrCertificateB s (chi * e)) := by
    simpa [by0I, lrCertificateB] using hby0Raw
  have hbeRaw := RationalEnclosure.contains_add hs
    (RationalEnclosure.contains_mul honeMinusS he)
  have hbe : (beI box).Contains (lrCertificateB s e) := by
    simpa [beI, lrCertificateB] using hbeRaw
  have hg0AD := payload.g0.sound terms hparts.2.2.1
    (IntervalAD.contains_parameter hv)
  have hg0 : ((payload.g0.evaluate terms (vAD payload)).value).Contains
      (lrCertificateG0 v) := hg0AD.1
  have hqBY0 := payload.qBY0.sound terms hparts.2.2.2.1 hby0
  have hqBE := payload.qBE.sound terms hparts.2.2.2.2.1 hbe
  have hqS := payload.qS.sound terms hparts.2.2.2.2.2.1 hs
  have hg0Parts :
      payload.g0.logV.check (vAD payload).value = true ∧
      payload.g0.logOnePlusV.check
        (LRG0ADCertificate.onePlusV (vAD payload)).value = true ∧
      payload.g0.logTwo.check (IntervalAD.const 2).value = true ∧
      (0 : ℚ) < (vAD payload).value.lower := by
    simpa [LRG0ADCertificate.check] using hparts.2.2.1
  have honePlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hv
  have htwoPlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 2) hv
  have hlogTwo := payload.g0.logTwo.sound terms hg0Parts.2.2.1
    (RationalEnclosure.contains_point 2)
  have hlogOnePlus := payload.g0.logOnePlusV.sound terms hg0Parts.2.1
    honePlusV
  have hlogTwoPlus := payload.logTwoPlusV.sound terms
    hparts.2.2.2.2.2.2.1 htwoPlusV
  have hlogFactor := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hlogTwo hlogOnePlus) hlogTwoPlus
  have hratio := RationalEnclosure.contains_div
    hparts.2.2.2.2.2.2.2.1 honePlusV hv
  have hqBEdiv := RationalEnclosure.contains_div
    hparts.2.2.2.2.2.2.2.1 hqBE hv
  have hdelta := RationalEnclosure.contains_sub hqS
    (RationalEnclosure.contains_mul hs hlogTwo)
  have hmain := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul honeMinusS hg0) hqBY0) hqBEdiv
  have hslopeCost := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul hs hratio)
    (RationalEnclosure.contains_add hlogTwo
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 2) hlogFactor))
  have hdeltaCost := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point 2)
      (RationalEnclosure.contains_div
        hparts.2.2.2.2.2.2.2.2.1 htwoPlusV honePlusV)) hdelta
  have htotal := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_sub hmain hslopeCost) hdeltaCost
  unfold evaluate lrGapBudgetSEChi
  dsimp only
  rw [← hxDef, ← hvDef]
  convert htotal using 1 <;> ring_nf

def nonnegative (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) ≤ (evaluate terms box payload).lower)

theorem nonnegative_sound (terms : ℕ) {box : CertificateBox}
    {s e chi : ℝ} {payload : Payload}
    (hs : (sI box).Contains s) (he : (eI box).Contains e)
    (hchi : (chiI box).Contains chi)
    (hcheck : check box payload = true)
    (hnonnegative : nonnegative terms box payload = true) :
    0 ≤ lrGapBudgetSEChi s e chi := by
  have hsound := evaluate_sound terms hs he hchi hcheck
  have hlower : (0 : ℝ) ≤ (evaluate terms box payload).lower := by
    exact_mod_cast (show (0 : ℚ) ≤ (evaluate terms box payload).lower by
      simpa [nonnegative] using hnonnegative)
  exact hlower.trans hsound.1

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  let vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel (radicandI box)
  let v := vSqrt.enclosure
  let vAD' := IntervalAD.parameter v
  { vSqrt := vSqrt
    g0 := LRG0ADCertificate.auto logFuel vAD'
    qBY0 := LRQZeroIntervalCertificate.auto sqrtFuel logFuel (by0I box)
    qBE := LRQZeroIntervalCertificate.auto sqrtFuel logFuel (beI box)
    qS := LRQZeroIntervalCertificate.auto sqrtFuel logFuel (sI box)
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.add (RationalEnclosure.point 2) v) }

def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  let payload := auto sqrtFuel logFuel box
  check box payload && nonnegative terms box payload

theorem autoAccepts_sound (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox)
    (haccept : autoAccepts terms sqrtFuel logFuel box = true) :
    ∀ s e chi, (sI box).Contains s → (eI box).Contains e →
      (chiI box).Contains chi → 0 ≤ lrGapBudgetSEChi s e chi := by
  intro s e chi hs he hchi
  have hparts : check box (auto sqrtFuel logFuel box) = true ∧
      nonnegative terms box (auto sqrtFuel logFuel box) = true := by
    simpa [autoAccepts] using haccept
  exact nonnegative_sound terms hs he hchi hparts.1 hparts.2

end LRGapBudgetSEEndpointValueCertificate
end CourtadeKumar
