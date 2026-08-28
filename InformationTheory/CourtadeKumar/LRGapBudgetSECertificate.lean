import InformationTheory.CourtadeKumar.LRHighShapeGapBudget
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Bounded-coordinate certificate for the gap-budget derivative

Here a `CertificateBox` is interpreted as a box in `(s,e,chi)`: its `k`
interval stores the bounded physical defect `e`.  Only `e` is marked as an
AD variable.  The `s` and `chi` intervals are range parameters, so the
resulting `derivK` enclosure is exactly `∂ₑ lrGapBudgetSEChi` throughout the
box rather than a derivative along a diagonal path.
-/

namespace CourtadeKumar

namespace IntervalAD

/-- A ranged parameter with all AD derivatives set to zero. -/
def parameter (value : RationalEnclosure) : IntervalAD where
  value := value
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 0

theorem contains_parameter {interval : RationalEnclosure} {x : ℝ}
    (hx : interval.Contains x) :
    (parameter interval).Contains x 0 0 0 := by
  simp only [Contains, parameter]
  have hzero : (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) := by
    norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
  exact ⟨hx, hzero, hzero, hzero⟩

end IntervalAD

namespace LRGapBudgetSECertificate

def sAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.parameter box.sInterval

/-- The `k` slot of the generic box stores `e` in this certificate. -/
def eAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableK box.kInterval

def chiAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.parameter box.chiInterval

def xAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.sub (IntervalAD.const 1)
    (IntervalAD.mul (chiAD box) (eAD box))

def radicandAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.const 1) (eAD box)) (xAD box)

structure Payload where
  vSqrt : RationalEnclosure.SqrtCertificate
  g0 : LRG0ADCertificate
  qBY0 : LRQADCertificate
  qBE : LRQADCertificate
  qS : LRQADCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate

def vAD (box : CertificateBox) (payload : Payload) : IntervalAD :=
  IntervalAD.sqrt payload.vSqrt (radicandAD box)

def by0AD (box : CertificateBox) : IntervalAD :=
  lrCertificateBAD (sAD box) (IntervalAD.mul (chiAD box) (eAD box))

def beAD (box : CertificateBox) : IntervalAD :=
  lrCertificateBAD (sAD box) (eAD box)

/-- Exact interval-AD transcription of `lrGapBudgetSEChi`. -/
def evaluate (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let one := IntervalAD.const 1
  let two := IntervalAD.const 2
  let s := sAD box
  let e := eAD box
  let chi := chiAD box
  let v := vAD box payload
  let by0 := lrCertificateBAD s (IntervalAD.mul chi e)
  let be := lrCertificateBAD s e
  let g0 := payload.g0.evaluate terms v
  let qBY0 := payload.qBY0.evaluate terms by0
  let qBE := payload.qBE.evaluate terms be
  let qS := payload.qS.evaluate terms s
  let logTwo := IntervalAD.log terms payload.g0.logTwo two
  let onePlusV := IntervalAD.add one v
  let twoPlusV := IntervalAD.add two v
  let logOnePlusV := IntervalAD.log terms payload.g0.logOnePlusV onePlusV
  let logTwoPlusV := IntervalAD.log terms payload.logTwoPlusV twoPlusV
  let logFactor := IntervalAD.sub
    (IntervalAD.add logTwo logOnePlusV) logTwoPlusV
  let ratio := IntervalAD.divPositive onePlusV v
  let delta := IntervalAD.sub qS (IntervalAD.mul s logTwo)
  let main := IntervalAD.add
    (IntervalAD.add
      (IntervalAD.mul (IntervalAD.sub one s) g0) qBY0)
    (IntervalAD.divPositive qBE v)
  let slopeCost := IntervalAD.mul (IntervalAD.mul s ratio)
    (IntervalAD.add logTwo
      (IntervalAD.mul (IntervalAD.const 2) logFactor))
  let deltaCost := IntervalAD.mul
    (IntervalAD.mul (IntervalAD.const 2)
      (IntervalAD.divPositive twoPlusV onePlusV)) delta
  IntervalAD.sub (IntervalAD.sub main slopeCost) deltaCost

def check (box : CertificateBox) (payload : Payload) : Bool :=
  let s := sAD box
  let v := vAD box payload
  let by0 := by0AD box
  let be := beAD box
  decide ((0 : ℚ) < (xAD box).value.lower ∧
      (0 : ℚ) < (radicandAD box).value.lower) &&
    IntervalAD.sqrtCheck (radicandAD box).value payload.vSqrt &&
    payload.g0.check v &&
    payload.qBY0.check by0.value &&
    payload.qBE.check be.value &&
    payload.qS.check s.value &&
    payload.logTwoPlusV.check
      (IntervalAD.add (IntervalAD.const 2) v).value &&
    decide ((0 : ℚ) < v.value.lower ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 2) v).value.lower)

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4000 in
theorem evaluate_sound (terms : ℕ) {box : CertificateBox}
    {s e chi : ℝ} {payload : Payload}
    (hs : box.sInterval.Contains s) (he : box.kInterval.Contains e)
    (hchi : box.chiInterval.Contains chi)
    (hcheck : check box payload = true) :
    (evaluate terms box payload).Contains
      (lrGapBudgetSEChi s e chi) 0
      (lrGapBudgetSEChiDerivE s e chi) 0 := by
  let sAD' := sAD box
  let eAD' := eAD box
  let chiAD' := chiAD box
  let xAD' := xAD box
  let radAD' := radicandAD box
  let vAD' := vAD box payload
  let by0AD' := by0AD box
  let beAD' := beAD box
  have hparts :
      ((0 : ℚ) < xAD'.value.lower ∧
        (0 : ℚ) < radAD'.value.lower) ∧
      IntervalAD.sqrtCheck radAD'.value payload.vSqrt = true ∧
      payload.g0.check vAD' = true ∧
      payload.qBY0.check by0AD'.value = true ∧
      payload.qBE.check beAD'.value = true ∧
      payload.qS.check sAD'.value = true ∧
      payload.logTwoPlusV.check
        (IntervalAD.add (IntervalAD.const 2) vAD').value = true ∧
      ((0 : ℚ) < vAD'.value.lower ∧
        (0 : ℚ) < (IntervalAD.add
          (IntervalAD.const 1) vAD').value.lower ∧
        (0 : ℚ) < (IntervalAD.add
          (IntervalAD.const 2) vAD').value.lower) := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with
      ⟨⟨⟨⟨⟨⟨⟨hcond, hsqrt⟩, hg0Check⟩, hqBY0Check⟩,
        hqBECheck⟩, hqSCheck⟩, hlogCheck⟩, hpositive⟩
    change (0 : ℚ) < xAD'.value.lower ∧
      (0 : ℚ) < radAD'.value.lower at hcond
    change IntervalAD.sqrtCheck radAD'.value payload.vSqrt = true at hsqrt
    change payload.g0.check vAD' = true at hg0Check
    change payload.qBY0.check by0AD'.value = true at hqBY0Check
    change payload.qBE.check beAD'.value = true at hqBECheck
    change payload.qS.check sAD'.value = true at hqSCheck
    change payload.logTwoPlusV.check
      (IntervalAD.add (IntervalAD.const 2) vAD').value = true at hlogCheck
    change (0 : ℚ) < vAD'.value.lower ∧
      (0 : ℚ) < (IntervalAD.add
        (IntervalAD.const 1) vAD').value.lower ∧
      (0 : ℚ) < (IntervalAD.add
        (IntervalAD.const 2) vAD').value.lower at hpositive
    exact ⟨hcond, hsqrt, hg0Check, hqBY0Check, hqBECheck,
      hqSCheck, hlogCheck, hpositive⟩
  have hvLowerRat : (0 : ℚ) < vAD'.value.lower :=
    hparts.2.2.2.2.2.2.2.1
  have honePlusLowerRat : (0 : ℚ) <
      (IntervalAD.add (IntervalAD.const 1) vAD').value.lower :=
    hparts.2.2.2.2.2.2.2.2.1
  have hsAD : sAD'.Contains s 0 0 0 :=
    IntervalAD.contains_parameter hs
  have heAD : eAD'.Contains e 0 1 0 :=
    IntervalAD.contains_variableK he
  have hchiAD : chiAD'.Contains chi 0 0 0 :=
    IntervalAD.contains_parameter hchi
  have hchiE := IntervalAD.contains_mul hchiAD heAD
  have hxAD : xAD'.Contains (1 - chi * e) 0 (-chi) 0 := by
    have h := IntervalAD.contains_sub (IntervalAD.contains_const 1) hchiE
    simpa [xAD', xAD, chiAD', chiAD, eAD', eAD] using h
  have hnum := IntervalAD.contains_sub (IntervalAD.contains_const 1) heAD
  have hradRaw := IntervalAD.contains_divPositive hparts.1.1 hnum hxAD
  have hrad : radAD'.Contains ((1 - e) / (1 - chi * e)) 0
      ((chi - 1) / (1 - chi * e) ^ 2) 0 := by
    change (radicandAD box).Contains ((1 - e) / (1 - chi * e)) 0
      ((chi - 1) / (1 - chi * e) ^ 2) 0
    convert hradRaw using 1 <;> ring_nf
  have hvRaw := IntervalAD.contains_sqrt hparts.2.1 hrad
  set v : ℝ := Real.sqrt ((1 - e) / (1 - chi * e)) with hvDef
  set v' : ℝ := (chi - 1) / (2 * v * (1 - chi * e) ^ 2) with hvPrimeDef
  have hvAD : vAD'.Contains v 0 v' 0 := by
    unfold vAD' vAD
    rw [hvDef, hvPrimeDef, hvDef]
    convert hvRaw using 1 <;> field_simp <;> ring
  have hxLower : (0 : ℝ) < xAD'.value.lower := by
    exact_mod_cast hparts.1.1
  have hxPos : 0 < 1 - chi * e := hxLower.trans_le hxAD.1.1
  have hvLower : (0 : ℝ) < vAD'.value.lower := by
    exact_mod_cast hvLowerRat
  have hvPos : 0 < v := hvLower.trans_le hvAD.1.1
  have hvPlus : 1 + v ≠ 0 := by linarith
  have htwoPlus : 2 + v ≠ 0 := by linarith
  have hchiEInput : (IntervalAD.mul chiAD' eAD').Contains
      (chi * e) 0 chi 0 := by
    simpa [chiAD', chiAD, eAD', eAD] using hchiE
  have hby0Raw := lrCertificateBAD_sound hsAD hchiEInput
  have hby0 : by0AD'.Contains (lrCertificateB s (chi * e)) 0
      ((1 - s) * chi) 0 := by
    unfold by0AD' by0AD
    convert hby0Raw using 1 <;> simp [lrCertificateBDeriv]
  have hbeRaw := lrCertificateBAD_sound hsAD heAD
  have hbe : beAD'.Contains (lrCertificateB s e) 0 (1 - s) 0 := by
    unfold beAD' beAD
    convert hbeRaw using 1 <;> simp [lrCertificateBDeriv]
  have hg0 := payload.g0.sound terms hparts.2.2.1 hvAD
  have hqBY0 := payload.qBY0.sound terms hparts.2.2.2.1 hby0
  have hqBE := payload.qBE.sound terms hparts.2.2.2.2.1 hbe
  have hqS := payload.qS.sound terms hparts.2.2.2.2.2.1 hsAD
  have hg0Parts :
      payload.g0.logV.check vAD'.value = true ∧
      payload.g0.logOnePlusV.check
        (LRG0ADCertificate.onePlusV vAD').value = true ∧
      payload.g0.logTwo.check (IntervalAD.const 2).value = true ∧
      (0 : ℚ) < vAD'.value.lower := by
    simpa [LRG0ADCertificate.check] using hparts.2.2.1
  have honePlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hvAD
  have htwoPlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 2) hvAD
  have hlogTwo := IntervalAD.contains_log terms hg0Parts.2.2.1
    (IntervalAD.contains_const 2)
  have hlogOnePlus := IntervalAD.contains_log terms hg0Parts.2.1 honePlusV
  have hlogTwoPlus := IntervalAD.contains_log terms
    hparts.2.2.2.2.2.2.1 htwoPlusV
  have hlogFactor := IntervalAD.contains_sub
    (IntervalAD.contains_add hlogTwo hlogOnePlus) hlogTwoPlus
  have hratio := IntervalAD.contains_divPositive
    hvLowerRat honePlusV hvAD
  have hqBEdiv := IntervalAD.contains_divPositive
    hvLowerRat hqBE hvAD
  have honeMinusS := IntervalAD.contains_sub
    (IntervalAD.contains_const 1) hsAD
  have hmain := IntervalAD.contains_add
    (IntervalAD.contains_add (IntervalAD.contains_mul honeMinusS hg0) hqBY0)
    hqBEdiv
  have hdelta := IntervalAD.contains_sub hqS
    (IntervalAD.contains_mul hsAD hlogTwo)
  have hslopeCost := IntervalAD.contains_mul
    (IntervalAD.contains_mul hsAD hratio)
    (IntervalAD.contains_add hlogTwo
      (IntervalAD.contains_mul (IntervalAD.contains_const 2) hlogFactor))
  have hdeltaCost := IntervalAD.contains_mul
    (IntervalAD.contains_mul (IntervalAD.contains_const 2)
      (IntervalAD.contains_divPositive
        honePlusLowerRat htwoPlusV honePlusV)) hdelta
  have htotal := IntervalAD.contains_sub
    (IntervalAD.contains_sub hmain hslopeCost) hdeltaCost
  have hvalue : lrGapBudgetSEChi s e chi =
      (1 - s) * lrCertificateG0 v +
          lrCertificateQ (lrCertificateB s (chi * e)) +
          lrCertificateQ (lrCertificateB s e) / v -
        s * (1 + v) / v *
          (Real.log 2 + 2 *
            (Real.log 2 + Real.log (1 + v) - Real.log (2 + v))) -
        2 * (2 + v) / (1 + v) *
          (lrCertificateQ s - s * Real.log 2) := by
    unfold lrGapBudgetSEChi
    dsimp only
  have hderiv : lrGapBudgetSEChiDerivE s e chi =
      (1 - s) * lrCertificateG0Prime v * v' +
          lrCertificateQPrime (lrCertificateB s (chi * e)) *
            ((1 - s) * chi) +
          (lrCertificateQPrime (lrCertificateB s e) * (1 - s) * v -
            lrCertificateQ (lrCertificateB s e) * v') / v ^ 2 -
        s *
          ((-v' / v ^ 2) *
              (Real.log 2 + 2 *
                (Real.log 2 + Real.log (1 + v) - Real.log (2 + v))) +
            ((1 + v) / v) *
              (2 * (v' / (1 + v) - v' / (2 + v)))) +
        2 * v' / (1 + v) ^ 2 *
          (lrCertificateQ s - s * Real.log 2) := by
    unfold lrGapBudgetSEChiDerivE
    dsimp only
  rw [hvalue, hderiv]
  unfold evaluate
  dsimp only
  convert htotal using 1 <;> ring_nf

def derivENonnegative (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) ≤ (evaluate terms box payload).derivK.lower)

/-- A kernel-checked box assertion that the bounded-coordinate gap budget is
nonnegative. -/
def budgetNonnegative (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) ≤ (evaluate terms box payload).value.lower)

theorem derivENonnegative_sound (terms : ℕ) {box : CertificateBox}
    {s e chi : ℝ} {payload : Payload}
    (hs : box.sInterval.Contains s) (he : box.kInterval.Contains e)
    (hchi : box.chiInterval.Contains chi)
    (hcheck : check box payload = true)
    (hnonnegative : derivENonnegative terms box payload = true) :
    0 ≤ lrGapBudgetSEChiDerivE s e chi := by
  have hsound := evaluate_sound terms hs he hchi hcheck
  have hlower : (0 : ℝ) ≤ (evaluate terms box payload).derivK.lower := by
    exact_mod_cast (show (0 : ℚ) ≤
      (evaluate terms box payload).derivK.lower by
        simpa [derivENonnegative] using hnonnegative)
  exact hlower.trans hsound.2.2.1.1

theorem budgetNonnegative_sound (terms : ℕ) {box : CertificateBox}
    {s e chi : ℝ} {payload : Payload}
    (hs : box.sInterval.Contains s) (he : box.kInterval.Contains e)
    (hchi : box.chiInterval.Contains chi)
    (hcheck : check box payload = true)
    (hnonnegative : budgetNonnegative terms box payload = true) :
    0 ≤ lrGapBudgetSEChi s e chi := by
  have hsound := evaluate_sound terms hs he hchi hcheck
  have hlower : (0 : ℝ) ≤ (evaluate terms box payload).value.lower := by
    exact_mod_cast (show (0 : ℚ) ≤
      (evaluate terms box payload).value.lower by
        simpa [budgetNonnegative] using hnonnegative)
  exact hlower.trans hsound.1.1

/-- A successful bounded-coordinate derivative leaf proves the derivative
needed by the original noncompact `k`-tail argument. -/
theorem certificateGapBudgetDerivK_nonnegative_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {payload : Payload}
    (hsBox : box.sInterval.Contains point.s)
    (heBox : box.kInterval.Contains (lrCertificateE point))
    (hchiBox : box.chiInterval.Contains point.chi)
    (hs : 0 ≤ point.s) (hv : 0 < lrCertificateV point)
    (hx : 0 < lrCertificateX point)
    (hcheck : check box payload = true)
    (hnonnegative : derivENonnegative terms box payload = true) :
    0 ≤ lrCertificateGapBudgetDerivK point := by
  apply lrCertificateGapBudgetDerivK_nonneg_of_derivE hs hv hx
  exact derivENonnegative_sound terms hsBox heBox hchiBox
    hcheck hnonnegative

/-- A successful bounded-coordinate value leaf also proves the original
coordinate gap budget nonnegative. -/
theorem certificateGapBudget_nonnegative_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {payload : Payload}
    (hsBox : box.sInterval.Contains point.s)
    (heBox : box.kInterval.Contains (lrCertificateE point))
    (hchiBox : box.chiInterval.Contains point.chi)
    (hv : 0 < lrCertificateV point)
    (hcheck : check box payload = true)
    (hnonnegative : budgetNonnegative terms box payload = true) :
    0 ≤ lrCertificateGapBudget point := by
  rw [lrCertificateGapBudget_eq_SEChi hv]
  exact budgetNonnegative_sound terms hsBox heBox hchiBox
    hcheck hnonnegative

/-- Deterministic proposal generation.  Soundness depends only on `check`. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  let vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
    (radicandAD box).value
  let v := IntervalAD.sqrt vSqrt (radicandAD box)
  { vSqrt := vSqrt
    g0 := LRG0ADCertificate.auto logFuel v
    qBY0 := LRQADCertificate.auto sqrtFuel logFuel (by0AD box).value
    qBE := LRQADCertificate.auto sqrtFuel logFuel (beAD box).value
    qS := LRQADCertificate.auto sqrtFuel logFuel (sAD box).value
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.add (IntervalAD.const 2) v).value }

end LRGapBudgetSECertificate

end CourtadeKumar
