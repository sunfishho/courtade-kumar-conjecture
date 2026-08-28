import InformationTheory.CourtadeKumar.LRGapBudgetSEEndpointMinorant

/-!
# Closed-endpoint interval certificate for the derivative minorant

This evaluator contains no `Q'` node.  Its sole entropy value `Q(s)` uses
the zero-aware value certificate, so accepted boxes may touch `s = 0`.
All generated square-root and logarithm data remain untrusted proposals and
are validated by the Boolean payload checker.
-/

namespace CourtadeKumar
namespace LRGapBudgetSEEndpointCertificate

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

structure Payload where
  vSqrt : RationalEnclosure.SqrtCertificate
  qS : LRQZeroIntervalCertificate
  logTwo : RationalEnclosure.LogIntervalCertificate
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate

def vI (payload : Payload) : RationalEnclosure := payload.vSqrt.enclosure

def onePlusVI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) (vI payload)

def twoPlusVI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 2) (vI payload)

def vSquareI (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative (vI payload) (vI payload)

def xSquareI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.mulNonnegative (xI box) (xI box)

def vPrimeI (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let denominator := RationalEnclosure.mulNonnegative
    (RationalEnclosure.mulNonnegative (RationalEnclosure.point 2) (vI payload))
    (xSquareI box)
  RationalEnclosure.div
    (RationalEnclosure.sub (chiI box) (RationalEnclosure.point 1))
    denominator

def evaluate (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let one := RationalEnclosure.point 1
  let two := RationalEnclosure.point 2
  let half := RationalEnclosure.point (1 / 2)
  let s := sI box
  let chi := chiI box
  let v := vI payload
  let vp := vPrimeI box payload
  let onePlusV := onePlusVI payload
  let twoPlusV := twoPlusVI payload
  let vSquare := vSquareI payload
  let logTwo := payload.logTwo.enclosure terms
  let logOnePlusV := payload.logOnePlusV.enclosure terms
  let logTwoPlusV := payload.logTwoPlusV.enclosure terms
  let g0Prime := RationalEnclosure.div
    (RationalEnclosure.sub logTwo logOnePlusV) vSquare
  let logFactor := RationalEnclosure.sub
    (RationalEnclosure.add logTwo logOnePlusV) logTwoPlusV
  let logFactorPrime := RationalEnclosure.sub
    (RationalEnclosure.div vp onePlusV)
    (RationalEnclosure.div vp twoPlusV)
  let ratio := RationalEnclosure.div onePlusV v
  let ratioPrime := RationalEnclosure.neg
    (RationalEnclosure.div vp vSquare)
  let qS := payload.qS.enclosure terms s
  let delta := RationalEnclosure.sub qS (RationalEnclosure.mul s logTwo)
  let first := RationalEnclosure.mul
    (RationalEnclosure.mul
      (RationalEnclosure.sub one s) g0Prime) vp
  let halfTerm := RationalEnclosure.mul
    (RationalEnclosure.mul half (RationalEnclosure.sub one s))
    (RationalEnclosure.add chi (RationalEnclosure.div one v))
  let slope := RationalEnclosure.mul s
    (RationalEnclosure.add
      (RationalEnclosure.mul ratioPrime
        (RationalEnclosure.add logTwo
          (RationalEnclosure.mul two logFactor)))
      (RationalEnclosure.mul ratio
        (RationalEnclosure.mul two logFactorPrime)))
  let deltaTerm := RationalEnclosure.mul
    (RationalEnclosure.div
      (RationalEnclosure.mul two vp)
      (RationalEnclosure.mulNonnegative onePlusV onePlusV)) delta
  RationalEnclosure.add
    (RationalEnclosure.sub (RationalEnclosure.add first halfTerm) slope)
    deltaTerm

def check (box : CertificateBox) (payload : Payload) : Bool :=
  decide ((0 : ℚ) < (xI box).lower ∧
      (0 : ℚ) < (radicandI box).lower) &&
    payload.vSqrt.check (radicandI box) &&
    payload.qS.check (sI box) &&
    payload.logTwo.check (RationalEnclosure.point 2) &&
    payload.logOnePlusV.check (onePlusVI payload) &&
    payload.logTwoPlusV.check (twoPlusVI payload) &&
    decide ((0 : ℚ) < (vI payload).lower ∧
      (0 : ℚ) < (onePlusVI payload).lower ∧
      (0 : ℚ) < (twoPlusVI payload).lower)

set_option maxHeartbeats 1200000 in
theorem evaluate_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {payload : Payload}
    (hpoint : box.Contains point) (hcheck : check box payload = true) :
    (evaluate terms box payload).Contains
      (lrGapBudgetSEChiDerivEEndpointMinorant
        point.s point.k point.chi) := by
  have hparts :
      ((0 : ℚ) < (xI box).lower ∧
        (0 : ℚ) < (radicandI box).lower) ∧
      payload.vSqrt.check (radicandI box) = true ∧
      payload.qS.check (sI box) = true ∧
      payload.logTwo.check (RationalEnclosure.point 2) = true ∧
      payload.logOnePlusV.check (onePlusVI payload) = true ∧
      payload.logTwoPlusV.check (twoPlusVI payload) = true ∧
      ((0 : ℚ) < (vI payload).lower ∧
        (0 : ℚ) < (onePlusVI payload).lower ∧
        (0 : ℚ) < (twoPlusVI payload).lower) := by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with
      ⟨⟨⟨⟨⟨⟨hcond, hsqrt⟩, hqSCheck⟩, hlogTwoCheck⟩,
        hlogOneCheck⟩, hlogTwoPlusCheck⟩, hpositive⟩
    exact ⟨hcond, hsqrt, hqSCheck, hlogTwoCheck,
      hlogOneCheck, hlogTwoPlusCheck, hpositive⟩
  have hs : (sI box).Contains point.s := ⟨hpoint.1, hpoint.2.1⟩
  have he : (eI box).Contains point.k :=
    ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchi : (chiI box).Contains point.chi :=
    ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hchiE := RationalEnclosure.contains_mul hchi he
  have hxRaw := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) hchiE
  set x : ℝ := 1 - point.chi * point.k with hxDef
  have hx : (xI box).Contains x := by
    rw [hxDef]
    simpa [xI] using hxRaw
  have hnum := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_point 1) he
  have hrad := RationalEnclosure.contains_div hparts.1.1 hnum hx
  set v : ℝ := Real.sqrt ((1 - point.k) / x) with hvDef
  have hvRaw := payload.vSqrt.sound hparts.2.1 hrad
  have hv : (vI payload).Contains v := by
    rw [hvDef]
    simpa [vI] using hvRaw
  have hvLowerNonneg : (0 : ℚ) ≤ (vI payload).lower :=
    hparts.2.2.2.2.2.2.1.le
  have hxLowerNonneg : (0 : ℚ) ≤ (xI box).lower := hparts.1.1.le
  have honePlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hv
  have htwoPlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 2) hv
  have hvSquare := RationalEnclosure.contains_mulNonnegative
    hvLowerNonneg hvLowerNonneg hv hv
  have hxSquare := RationalEnclosure.contains_mulNonnegative
    hxLowerNonneg hxLowerNonneg hx hx
  have htwoV := RationalEnclosure.contains_mulNonnegative
    (by norm_num [RationalEnclosure.point] :
      (0 : ℚ) ≤ (RationalEnclosure.point 2).lower)
    hvLowerNonneg (RationalEnclosure.contains_point 2) hv
  have hden := RationalEnclosure.contains_mulNonnegative
    (by
      dsimp [RationalEnclosure.mulNonnegative, RationalEnclosure.point]
      positivity)
    (by
      dsimp [xSquareI, RationalEnclosure.mulNonnegative]
      exact mul_nonneg hxLowerNonneg hxLowerNonneg)
    htwoV hxSquare
  have hdenLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative
        (RationalEnclosure.mulNonnegative
          (RationalEnclosure.point 2) (vI payload))
        (xSquareI box)).lower := by
    dsimp [xSquareI, RationalEnclosure.mulNonnegative,
      RationalEnclosure.point]
    exact mul_pos (mul_pos (by norm_num) hparts.2.2.2.2.2.2.1)
      (mul_pos hparts.1.1 hparts.1.1)
  have hvpRaw := RationalEnclosure.contains_div hdenLower
    (RationalEnclosure.contains_sub hchi
      (RationalEnclosure.contains_point 1)) hden
  set vp : ℝ := (point.chi - 1) / (2 * v * x ^ 2) with hvpDef
  have hvp : (vPrimeI box payload).Contains vp := by
    rw [hvpDef]
    convert hvpRaw using 1 <;> ring
  have hlogTwo := payload.logTwo.sound terms
    hparts.2.2.2.1 (RationalEnclosure.contains_point 2)
  have hlogOne := payload.logOnePlusV.sound terms
    hparts.2.2.2.2.1 honePlusV
  have hlogTwoPlus := payload.logTwoPlusV.sound terms
    hparts.2.2.2.2.2.1 htwoPlusV
  have hqS := payload.qS.sound terms hparts.2.2.1 hs
  have hvSquareLower : (0 : ℚ) < (vSquareI payload).lower := by
    dsimp [vSquareI, RationalEnclosure.mulNonnegative]
    exact mul_pos hparts.2.2.2.2.2.2.1 hparts.2.2.2.2.2.2.1
  have honePlusLower : (0 : ℚ) < (onePlusVI payload).lower :=
    hparts.2.2.2.2.2.2.2.1
  have htwoPlusLower : (0 : ℚ) < (twoPlusVI payload).lower :=
    hparts.2.2.2.2.2.2.2.2
  have hg0Prime := RationalEnclosure.contains_div hvSquareLower
    (RationalEnclosure.contains_sub hlogTwo hlogOne) hvSquare
  have hlogFactor := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hlogTwo hlogOne) hlogTwoPlus
  have hlogFactorPrime := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_div honePlusLower hvp honePlusV)
    (RationalEnclosure.contains_div htwoPlusLower hvp htwoPlusV)
  have hratio := RationalEnclosure.contains_div
    hparts.2.2.2.2.2.2.1 honePlusV hv
  have hratioPrime := RationalEnclosure.contains_neg
    (RationalEnclosure.contains_div hvSquareLower hvp hvSquare)
  have hdelta := RationalEnclosure.contains_sub hqS
    (RationalEnclosure.contains_mul hs hlogTwo)
  have hfirst := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_point 1) hs) hg0Prime) hvp
  have hhalfTerm := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point (1 / 2))
      (RationalEnclosure.contains_sub
        (RationalEnclosure.contains_point 1) hs))
    (RationalEnclosure.contains_add hchi
      (RationalEnclosure.contains_div
        hparts.2.2.2.2.2.2.1
        (RationalEnclosure.contains_point 1) hv))
  have hslope := RationalEnclosure.contains_mul hs
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hratioPrime
        (RationalEnclosure.contains_add hlogTwo
          (RationalEnclosure.contains_mul
            (RationalEnclosure.contains_point 2) hlogFactor)))
      (RationalEnclosure.contains_mul hratio
        (RationalEnclosure.contains_mul
          (RationalEnclosure.contains_point 2) hlogFactorPrime)))
  have honePlusSquare := RationalEnclosure.contains_mulNonnegative
    honePlusLower.le honePlusLower.le honePlusV honePlusV
  have honePlusSquareLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative
        (onePlusVI payload) (onePlusVI payload)).lower := by
    dsimp [RationalEnclosure.mulNonnegative]
    positivity
  have hdeltaTerm := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_div honePlusSquareLower
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 2) hvp) honePlusSquare) hdelta
  have htotal := RationalEnclosure.contains_add
    (RationalEnclosure.contains_sub
      (RationalEnclosure.contains_add hfirst hhalfTerm) hslope) hdeltaTerm
  unfold evaluate lrGapBudgetSEChiDerivEEndpointMinorant
    lrCertificateG0Prime
  dsimp only
  rw [← hxDef, ← hvDef, ← hvpDef]
  convert htotal using 1 <;> ring_nf

def nonnegative (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) ≤ (evaluate terms box payload).lower)

theorem nonnegative_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {payload : Payload}
    (hpoint : box.Contains point) (hcheck : check box payload = true)
    (hnonnegative : nonnegative terms box payload = true) :
    0 ≤ lrGapBudgetSEChiDerivEEndpointMinorant
      point.s point.k point.chi := by
  have hsound := evaluate_sound terms hpoint hcheck
  have hlower : (0 : ℝ) ≤ (evaluate terms box payload).lower := by
    exact_mod_cast (show (0 : ℚ) ≤ (evaluate terms box payload).lower by
      simpa [nonnegative] using hnonnegative)
  exact hlower.trans hsound.1

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  let vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel (radicandI box)
  let v := vSqrt.enclosure
  { vSqrt := vSqrt
    qS := LRQZeroIntervalCertificate.auto sqrtFuel logFuel (sI box)
    logTwo := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.point 2)
    logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.add (RationalEnclosure.point 1) v)
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (RationalEnclosure.add (RationalEnclosure.point 2) v) }

def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_data : Unit) : Bool :=
  let payload := auto sqrtFuel logFuel box
  check box payload && nonnegative terms box payload

theorem autoAccepts_sound (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (data : Unit)
    (haccept : autoAccepts terms sqrtFuel logFuel box data = true) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  intro point hpoint hrelevant
  have hparts : check box (auto sqrtFuel logFuel box) = true ∧
      nonnegative terms box (auto sqrtFuel logFuel box) = true := by
    simpa [autoAccepts] using haccept
  have hminorant := nonnegative_sound terms hpoint hparts.1 hparts.2
  exact lrGapBudgetSEChiDerivE_nonnegative_of_endpointMinorant
    ⟨hrelevant.1.1, hrelevant.1.2.trans (by norm_num)⟩
    hrelevant.2.1 hrelevant.2.2.1 hminorant

end LRGapBudgetSEEndpointCertificate
end CourtadeKumar
