import InformationTheory.CourtadeKumar.IntervalADElementary
import InformationTheory.CourtadeKumar.LRDeterminantIdealIntervalEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantIdealHSlopeBounds

/-!
# Shared primitive AD graph for ideal determinant replays

This source-only checkpoint is the common concrete layer for the
`L₀ = 7 log 2` low-`k` replay and the `L₀ = 14 log 2` restricted replay.
It verifies stable positive-input interval-AD nodes for `H` and `QChi`,
packages the three nonlinear primitives with their real derivatives, and
checks one complete shared output, `Lambda/2`.

Boxes meeting `chi = 0` deliberately remain on the existing natural,
value-only path.  Generated payloads contain only checked rational log
certificates; there are no proof fields or executable proof shortcuts.
-/

namespace CourtadeKumar
namespace LRLowKIdealSharedPrimitiveAD

/-! ## Replay-independent configuration -/

inductive TargetMode where
  | globalTail
  | endpoint
  deriving DecidableEq, Repr

structure Config where
  l0Scale : ℚ
  margin : ℚ
  mode : TargetMode
  deriving Repr

noncomputable def Config.l0 (config : Config) : ℝ :=
  (config.l0Scale : ℝ) * Real.log 2

def lowKMiddleConfig : Config :=
  { l0Scale := 7, margin := 19 / 50, mode := .globalTail }

def lowKUpperConfig : Config :=
  { l0Scale := 7, margin := 19 / 50, mode := .endpoint }

def restrictedGlobalConfig : Config :=
  { l0Scale := 14, margin := 3 / 5, mode := .globalTail }

def restrictedEndpointConfig : Config :=
  { l0Scale := 14, margin := 3 / 5, mode := .endpoint }

/-! ## Stable positive-input entropy primitives -/

noncomputable def idealHPrime (t : ℝ) : ℝ :=
  (t - Real.log (1 + t)) / t ^ 2

/-- Cancellation-free slope interval.  Its strictly positive lower endpoint
is computed only on the positive-input mean-value path; boxes touching the
zero face continue to use the separate natural evaluator. -/
def idealHSlopeI (input : RationalEnclosure) : RationalEnclosure :=
  lrDeterminantIdealHSlopeEnclosure input

theorem idealHSlopeI_sound
    {input : RationalEnclosure} {t : ℝ}
    (hlower : (0 : ℚ) < input.lower) (ht : input.Contains t) :
    (idealHSlopeI input).Contains (idealHPrime t) := by
  simpa [idealHSlopeI, idealHPrime] using
    lrDeterminantIdealHSlopeEnclosure_contains hlower ht

/-- Stable unary node: the verified zero-aware certificate provides the
value, while the checked cancellation-free interval encloses the real slope
on positive inputs. -/
def idealHValueI (terms : ℕ)
    (certificate : LRDeterminantIdealHCertificate)
    (input : RationalEnclosure) : RationalEnclosure :=
  let logI := certificate.logOnePlus.enclosure terms
  ⟨((1 + input.lower) / input.lower) * logI.lower,
    ((1 + input.upper) / input.upper) * logI.upper⟩

theorem idealH_logCheck_of_check
    {input : RationalEnclosure}
    {certificate : LRDeterminantIdealHCertificate}
    (hlower : (0 : ℚ) < input.lower)
    (hcheck : certificate.check input = true) :
    certificate.logOnePlus.check
        (LRDeterminantIdealHCertificate.onePlusI input) = true := by
  have hlo : input.lower ≠ 0 := ne_of_gt hlower
  have houter :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper) = true ∧
      (if input.lower = 0 then
        if input.upper = 0 then true
        else decide ((0 : ℚ) < input.upper) &&
          certificate.logOnePlus.check
            (LRDeterminantIdealHCertificate.endpointOnePlusI input)
      else decide ((0 : ℚ) < input.lower) &&
        certificate.logOnePlus.check
          (LRDeterminantIdealHCertificate.onePlusI input)) = true := by
    simpa [LRDeterminantIdealHCertificate.check] using hcheck
  have hbranch : (0 : ℚ) < input.lower ∧
      certificate.logOnePlus.check
        (LRDeterminantIdealHCertificate.onePlusI input) = true := by
    simpa [hlo] using houter.2
  exact hbranch.2

/-- On a positive input interval, monotonicity of `H` permits evaluating its
two endpoint values separately.  This avoids the dependency loss in the
ordinary interval expression `(1+t) * log (1+t) / t`. -/
theorem idealHValueI_sound
    (terms : ℕ) {certificate : LRDeterminantIdealHCertificate}
    {input : RationalEnclosure} {t : ℝ}
    (hlower : (0 : ℚ) < input.lower)
    (hcheck : certificate.check input = true)
    (ht : input.Contains t) :
    (idealHValueI terms certificate input).Contains
      (lrDeterminantIdealH t) := by
  have hloReal : 0 < (input.lower : ℝ) := by
    exact_mod_cast hlower
  have hvalidReal : (input.lower : ℝ) ≤ (input.upper : ℝ) :=
    ht.1.trans ht.2
  have hvalid : input.lower ≤ input.upper := by
    exact_mod_cast hvalidReal
  have hupReal : 0 < (input.upper : ℝ) :=
    hloReal.trans_le hvalidReal
  have honeLower :
      (LRDeterminantIdealHCertificate.onePlusI input).Contains
        (1 + (input.lower : ℝ)) := by
    constructor <;>
      norm_num [LRDeterminantIdealHCertificate.onePlusI,
        RationalEnclosure.add, RationalEnclosure.point,
        RationalEnclosure.Contains] at * <;> assumption
  have honeUpper :
      (LRDeterminantIdealHCertificate.onePlusI input).Contains
        (1 + (input.upper : ℝ)) := by
    constructor <;>
      norm_num [LRDeterminantIdealHCertificate.onePlusI,
        RationalEnclosure.add, RationalEnclosure.point,
        RationalEnclosure.Contains] at * <;> assumption
  have hlogCheck := idealH_logCheck_of_check hlower hcheck
  have hlogLower := certificate.logOnePlus.sound terms hlogCheck honeLower
  have hlogUpper := certificate.logOnePlus.sound terms hlogCheck honeUpper
  have hfactorLower :
      0 ≤ ((((1 + input.lower) / input.lower : ℚ) : ℝ)) := by
    positivity
  have hfactorUpper :
      0 ≤ ((((1 + input.upper) / input.upper : ℚ) : ℝ)) := by
    have hup : (0 : ℚ) < input.upper := hlower.trans_le hvalid
    exact_mod_cast (div_nonneg (by linarith : (0 : ℚ) ≤ 1 + input.upper)
      hup.le)
  have hscaledLower :=
    mul_le_mul_of_nonneg_left hlogLower.1 hfactorLower
  have hscaledUpper :=
    mul_le_mul_of_nonneg_left hlogUpper.2 hfactorUpper
  have hformulaLower :
      ((((1 + input.lower) / input.lower : ℚ) : ℝ)) *
          Real.log (1 + (input.lower : ℝ)) =
        lrDeterminantIdealH (input.lower : ℝ) := by
    unfold lrDeterminantIdealH
    rw [if_neg hloReal.ne']
    norm_num
    ring
  have hformulaUpper :
      ((((1 + input.upper) / input.upper : ℚ) : ℝ)) *
          Real.log (1 + (input.upper : ℝ)) =
        lrDeterminantIdealH (input.upper : ℝ) := by
    unfold lrDeterminantIdealH
    rw [if_neg hupReal.ne']
    norm_num
    ring
  have htNonnegative : 0 ≤ t := hloReal.le.trans ht.1
  have hmonoLower :=
    lrDeterminantIdealH_mono_nonnegative hloReal.le ht.1
  have hmonoUpper :=
    lrDeterminantIdealH_mono_nonnegative htNonnegative ht.2
  constructor
  · calc
      (((idealHValueI terms certificate input).lower : ℚ) : ℝ) =
          ((((1 + input.lower) / input.lower : ℚ) : ℝ)) *
            ((certificate.logOnePlus.enclosure terms).lower : ℝ) := by
        norm_num [idealHValueI]
      _ ≤ ((((1 + input.lower) / input.lower : ℚ) : ℝ)) *
            Real.log (1 + (input.lower : ℝ)) := hscaledLower
      _ = lrDeterminantIdealH (input.lower : ℝ) := hformulaLower
      _ ≤ lrDeterminantIdealH t := hmonoLower
  · calc
      lrDeterminantIdealH t ≤
          lrDeterminantIdealH (input.upper : ℝ) := hmonoUpper
      _ = ((((1 + input.upper) / input.upper : ℚ) : ℝ)) *
            Real.log (1 + (input.upper : ℝ)) := hformulaUpper.symm
      _ ≤ ((((1 + input.upper) / input.upper : ℚ) : ℝ)) *
            ((certificate.logOnePlus.enclosure terms).upper : ℝ) :=
        hscaledUpper
      _ = (((idealHValueI terms certificate input).upper : ℚ) : ℝ) := by
        norm_num [idealHValueI]

def idealHAD (terms : ℕ)
    (certificate : LRDeterminantIdealHCertificate)
    (input : IntervalAD) : IntervalAD :=
  IntervalAD.unary
    (idealHValueI terms certificate input.value)
    (idealHSlopeI input.value) input

theorem idealHAD_sound
    (terms : ℕ) {certificate : LRDeterminantIdealHCertificate}
    {input : IntervalAD} {t ts tk tchi : ℝ}
    (hlower : (0 : ℚ) < input.value.lower)
    (hcheck : certificate.check input.value = true)
    (hinput : input.Contains t ts tk tchi) :
    (idealHAD terms certificate input).Contains
      (lrDeterminantIdealH t)
      (idealHPrime t * ts) (idealHPrime t * tk)
      (idealHPrime t * tchi) := by
  exact IntervalAD.contains_unary
    (idealHValueI_sound terms hlower hcheck hinput.1)
    (idealHSlopeI_sound hlower hinput.1) hinput

noncomputable def idealQChiPrime (chi : ℝ) : ℝ :=
  lrSmallSBridgeQChiNumerator chi / (1 + chi) ^ 2

/-- Intersection of two already-sound scalar enclosures.  It is deliberately
defined with exact rational `max`/`min`, so tightening remains executable. -/
def tightIntersection (a b : RationalEnclosure) : RationalEnclosure :=
  ⟨max a.lower b.lower, min a.upper b.upper⟩

theorem tightIntersection_contains
    {a b : RationalEnclosure} {x : ℝ}
    (ha : a.Contains x) (hb : b.Contains x) :
    (tightIntersection a b).Contains x := by
  constructor
  · by_cases hab : a.lower ≤ b.lower
    · simpa [tightIntersection, max_eq_right hab] using hb.1
    · have hba : b.lower ≤ a.lower := le_of_not_ge hab
      simpa [tightIntersection, max_eq_left hba] using ha.1
  · by_cases hab : a.upper ≤ b.upper
    · simpa [tightIntersection, min_eq_left hab] using ha.2
    · have hba : b.upper ≤ a.upper := le_of_not_ge hab
      simpa [tightIntersection, min_eq_right hba] using hb.2

/-- The checked formula enclosure intersected with the global calculus bound
`-2/7 ≤ qChi ≤ 0`. -/
def idealQChiValueI (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRDeterminantIdealQChiCertificate) :
    RationalEnclosure :=
  tightIntersection (certificate.enclosure terms input)
    lrSmallSBridgeQChiEndpointEnclosure

theorem idealQChiValueI_sound
    (terms : ℕ) {input : RationalEnclosure} {chi : ℝ}
    {certificate : LRDeterminantIdealQChiCertificate}
    (hcheck : certificate.check input = true)
    (hchi : input.Contains chi) :
    (idealQChiValueI terms input certificate).Contains
      (lrSmallSBridgeQChi chi) := by
  have houter :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
        input.upper ≤ 1) = true ∧
      (if input.lower = 0 then
        if input.upper = 0 then true
        else decide (input.upper ≤ (1 / 4 : ℚ)) &&
          certificate.logChi.check (RationalEnclosure.point input.upper)
      else decide ((0 : ℚ) < input.lower) &&
        certificate.logChi.check input) = true := by
    simpa [LRDeterminantIdealQChiCertificate.check] using hcheck
  have hdomain : (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper ≤ 1 := by
    simpa using houter.1
  have hloReal : (0 : ℝ) ≤ (input.lower : ℝ) := by
    exact_mod_cast hdomain.1
  have hupReal : (input.upper : ℝ) ≤ 1 := by
    exact_mod_cast hdomain.2.2
  have hchiUnit : chi ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hloReal.trans hchi.1, hchi.2.trans hupReal⟩
  exact tightIntersection_contains
    (certificate.sound terms hcheck hchi)
    (lrSmallSBridgeQChiEndpointEnclosure_sound hchiUnit)

def qChiOnePlusI (input : RationalEnclosure) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1) input

def idealQChiSlopeI (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRDeterminantIdealQChiCertificate) :
    RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.add
      (RationalEnclosure.add
        (certificate.logChi.enclosure terms)
        (RationalEnclosure.point 1)) input)
    (RationalEnclosure.mulNonnegative
      (qChiOnePlusI input) (qChiOnePlusI input))

def idealQChiAD (terms : ℕ)
    (certificate : LRDeterminantIdealQChiCertificate)
    (input : IntervalAD) : IntervalAD :=
  IntervalAD.unary
    (idealQChiValueI terms input.value certificate)
    (idealQChiSlopeI terms input.value certificate) input

theorem qChi_logCheck_of_check
    {input : RationalEnclosure}
    {certificate : LRDeterminantIdealQChiCertificate}
    (hlower : (0 : ℚ) < input.lower)
    (hcheck : certificate.check input = true) :
    certificate.logChi.check input = true := by
  have hlo : input.lower ≠ 0 := ne_of_gt hlower
  have houter :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
        input.upper ≤ 1) = true ∧
      (if input.lower = 0 then
        if input.upper = 0 then true
        else decide (input.upper ≤ (1 / 4 : ℚ)) &&
          certificate.logChi.check (RationalEnclosure.point input.upper)
      else decide ((0 : ℚ) < input.lower) &&
        certificate.logChi.check input) = true := by
    simpa [LRDeterminantIdealQChiCertificate.check] using hcheck
  have hbranch : (0 : ℚ) < input.lower ∧
      certificate.logChi.check input = true := by
    simpa [hlo] using houter.2
  exact hbranch.2

theorem idealQChiSlopeI_sound
    (terms : ℕ) {input : RationalEnclosure} {chi : ℝ}
    {certificate : LRDeterminantIdealQChiCertificate}
    (hlower : (0 : ℚ) < input.lower)
    (hlog : certificate.logChi.check input = true)
    (hchi : input.Contains chi) :
    (idealQChiSlopeI terms input certificate).Contains
      (idealQChiPrime chi) := by
  have hlogSound := certificate.logChi.sound terms hlog hchi
  have hone := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hchi
  have honeLower : (0 : ℚ) < (qChiOnePlusI input).lower := by
    dsimp [qChiOnePlusI, RationalEnclosure.add,
      RationalEnclosure.point]
    linarith
  have hsquare := RationalEnclosure.contains_mulNonnegative
    honeLower.le honeLower.le hone hone
  have hsquareLower : (0 : ℚ) <
      (RationalEnclosure.mulNonnegative
        (qChiOnePlusI input) (qChiOnePlusI input)).lower := by
    dsimp [RationalEnclosure.mulNonnegative]
    exact mul_pos honeLower honeLower
  have hnum := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add hlogSound
      (RationalEnclosure.contains_point 1)) hchi
  have hquot := RationalEnclosure.contains_div
    hsquareLower hnum hsquare
  simpa [idealQChiSlopeI, idealQChiPrime,
    lrSmallSBridgeQChiNumerator, pow_two] using hquot

theorem idealQChiAD_sound
    (terms : ℕ) {certificate : LRDeterminantIdealQChiCertificate}
    {input : IntervalAD} {chi chis chik chichi : ℝ}
    (hlower : (0 : ℚ) < input.value.lower)
    (hcheck : certificate.check input.value = true)
    (hinput : input.Contains chi chis chik chichi) :
    (idealQChiAD terms certificate input).Contains
      (lrSmallSBridgeQChi chi)
      (idealQChiPrime chi * chis)
      (idealQChiPrime chi * chik)
      (idealQChiPrime chi * chichi) := by
  exact IntervalAD.contains_unary
    (idealQChiValueI_sound terms hcheck hinput.1)
    (idealQChiSlopeI_sound terms hlower
      (qChi_logCheck_of_check hlower hcheck) hinput.1) hinput

/-! ## Shared payload and coordinate graph -/

structure Payload where
  logTwo : RationalEnclosure.LogIntervalCertificate
  logFourThird : RationalEnclosure.LogIntervalCertificate
  logK : RationalEnclosure.LogIntervalCertificate
  logOnePlusK : RationalEnclosure.LogIntervalCertificate
  logOnePlusKChi : RationalEnclosure.LogIntervalCertificate
  logDArg : RationalEnclosure.LogIntervalCertificate
  hK : LRDeterminantIdealHCertificate
  hKChi : LRDeterminantIdealHCertificate
  qChi : LRDeterminantIdealQChiCertificate

def mulNonnegativeAD (a b : IntervalAD) : IntervalAD :=
  let raw := IntervalAD.mul a b
  { raw with value := RationalEnclosure.mulNonnegative a.value b.value }

theorem mulNonnegativeAD_sound
    {a b : IntervalAD} {av as ak ac bv bs bk bc : ℝ}
    (haLower : (0 : ℚ) ≤ a.value.lower)
    (hbLower : (0 : ℚ) ≤ b.value.lower)
    (ha : a.Contains av as ak ac) (hb : b.Contains bv bs bk bc) :
    (mulNonnegativeAD a b).Contains (av * bv)
      (as * bv + av * bs) (ak * bv + av * bk)
      (ac * bv + av * bc) := by
  have hraw := IntervalAD.contains_mul ha hb
  exact ⟨RationalEnclosure.contains_mulNonnegative
    haLower hbLower ha.1 hb.1, hraw.2⟩

def kAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableK box.kInterval

def chiAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableChi box.chiInterval

def kChiAD (box : CertificateBox) : IntervalAD :=
  mulNonnegativeAD (kAD box) (chiAD box)

def onePlusKAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) (kAD box)

def onePlusKChiAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) (kChiAD box)

def onePlusChiAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) (chiAD box)

def twoKAD (box : CertificateBox) : IntervalAD :=
  mulNonnegativeAD (IntervalAD.const 2) (kAD box)

def fourKPlusThreeAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add
    (mulNonnegativeAD (IntervalAD.const 4) (kAD box))
    (IntervalAD.const 3)

def dArgAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1)
    (IntervalAD.invPositive (twoKAD box))

def Payload.payloadCheck (box : CertificateBox)
    (payload : Payload) : Bool :=
  decide ((0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
    (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
    box.chiHi ≤ 1) &&
  decide ((0 : ℚ) < (onePlusChiAD box).value.lower ∧
    (0 : ℚ) < (twoKAD box).value.lower ∧
    (0 : ℚ) < (fourKPlusThreeAD box).value.lower) &&
  payload.logTwo.check (IntervalAD.const 2).value &&
  payload.logFourThird.check (IntervalAD.const (4 / 3)).value &&
  payload.logK.check (kAD box).value &&
  payload.logOnePlusK.check (onePlusKAD box).value &&
  payload.logOnePlusKChi.check (onePlusKChiAD box).value &&
  payload.logDArg.check (dArgAD box).value &&
  payload.hK.check (kAD box).value &&
  payload.hKChi.check (kChiAD box).value &&
  payload.qChi.check (chiAD box).value

structure Payload.Valid (box : CertificateBox)
    (payload : Payload) : Prop where
  domain : (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
    (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
    box.chiHi ≤ 1
  denominators : (0 : ℚ) < (onePlusChiAD box).value.lower ∧
    (0 : ℚ) < (twoKAD box).value.lower ∧
    (0 : ℚ) < (fourKPlusThreeAD box).value.lower
  logTwo : payload.logTwo.check (IntervalAD.const 2).value = true
  logFourThird : payload.logFourThird.check
    (IntervalAD.const (4 / 3)).value = true
  logK : payload.logK.check (kAD box).value = true
  logOnePlusK : payload.logOnePlusK.check
    (onePlusKAD box).value = true
  logOnePlusKChi : payload.logOnePlusKChi.check
    (onePlusKChiAD box).value = true
  logDArg : payload.logDArg.check (dArgAD box).value = true
  hK : payload.hK.check (kAD box).value = true
  hKChi : payload.hKChi.check (kChiAD box).value = true
  qChi : payload.qChi.check (chiAD box).value = true

theorem Payload.valid_of_payloadCheck
    {box : CertificateBox} {payload : Payload}
    (hcheck : payload.payloadCheck box = true) :
    payload.Valid box := by
  have h :
      ((0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1) ∧
      ((0 : ℚ) < (onePlusChiAD box).value.lower ∧
        (0 : ℚ) < (twoKAD box).value.lower ∧
        (0 : ℚ) < (fourKPlusThreeAD box).value.lower) ∧
      payload.logTwo.check (IntervalAD.const 2).value = true ∧
      payload.logFourThird.check
        (IntervalAD.const (4 / 3)).value = true ∧
      payload.logK.check (kAD box).value = true ∧
      payload.logOnePlusK.check (onePlusKAD box).value = true ∧
      payload.logOnePlusKChi.check (onePlusKChiAD box).value = true ∧
      payload.logDArg.check (dArgAD box).value = true ∧
      payload.hK.check (kAD box).value = true ∧
      payload.hKChi.check (kChiAD box).value = true ∧
      payload.qChi.check (chiAD box).value = true := by
    simpa [Payload.payloadCheck, and_assoc] using hcheck
  rcases h with ⟨hdomain, hdenominators, hlogTwo, hlogFourThird,
    hlogK, hlogOnePlusK, hlogOnePlusKChi, hlogDArg,
    hhK, hhKChi, hqChi⟩
  exact ⟨hdomain, hdenominators, hlogTwo, hlogFourThird,
    hlogK, hlogOnePlusK, hlogOnePlusKChi, hlogDArg,
    hhK, hhKChi, hqChi⟩

def Payload.auto (logFuel : ℕ) (box : CertificateBox) : Payload where
  logTwo := RationalEnclosure.autoLogIntervalCertificate logFuel
    (IntervalAD.const 2).value
  logFourThird := RationalEnclosure.autoLogIntervalCertificate logFuel
    (IntervalAD.const (4 / 3)).value
  logK := RationalEnclosure.autoLogIntervalCertificate logFuel
    (kAD box).value
  logOnePlusK := RationalEnclosure.autoLogIntervalCertificate logFuel
    (onePlusKAD box).value
  logOnePlusKChi := RationalEnclosure.autoLogIntervalCertificate logFuel
    (onePlusKChiAD box).value
  logDArg := RationalEnclosure.autoLogIntervalCertificate logFuel
    (dArgAD box).value
  hK := LRDeterminantIdealHCertificate.auto logFuel (kAD box).value
  hKChi := LRDeterminantIdealHCertificate.auto logFuel (kChiAD box).value
  qChi := LRDeterminantIdealQChiCertificate.auto logFuel (chiAD box).value

/-! ## The three shared nonlinear primitives -/

structure PrimitiveAD where
  hK : IntervalAD
  hKChi : IntervalAD
  qChi : IntervalAD

def evaluatePrimitives (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : PrimitiveAD where
  hK := idealHAD terms payload.hK (kAD box)
  hKChi := idealHAD terms payload.hKChi (kChiAD box)
  qChi := idealQChiAD terms payload.qChi (chiAD box)

theorem evaluatePrimitives_sound
    (terms : ℕ) {box : CertificateBox} {payload : Payload}
    (hvalid : payload.Valid box)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (evaluatePrimitives terms box payload).hK.Contains
        (lrDeterminantIdealH point.k) 0 (idealHPrime point.k) 0 ∧
      (evaluatePrimitives terms box payload).hKChi.Contains
        (lrDeterminantIdealH (point.k * point.chi)) 0
          (idealHPrime (point.k * point.chi) * point.chi)
          (idealHPrime (point.k * point.chi) * point.k) ∧
      (evaluatePrimitives terms box payload).qChi.Contains
        (lrSmallSBridgeQChi point.chi) 0 0
          (idealQChiPrime point.chi) := by
  have hk : (kAD box).Contains point.k 0 1 0 :=
    IntervalAD.contains_variableK
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchi : (chiAD box).Contains point.chi 0 0 1 :=
    IntervalAD.contains_variableChi
      ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hkLower : (0 : ℚ) ≤ (kAD box).value.lower := by
    simpa [kAD, CertificateBox.kInterval] using hvalid.domain.1.le
  have hchiLower : (0 : ℚ) ≤ (chiAD box).value.lower := by
    simpa [chiAD, CertificateBox.chiInterval] using hvalid.domain.2.2.1.le
  have hkChi := mulNonnegativeAD_sound hkLower hchiLower hk hchi
  have hkStrict : (0 : ℚ) < (kAD box).value.lower := by
    simpa [kAD, CertificateBox.kInterval] using hvalid.domain.1
  have hchiStrict : (0 : ℚ) < (chiAD box).value.lower := by
    simpa [chiAD, CertificateBox.chiInterval] using hvalid.domain.2.2.1
  have hkChiStrict : (0 : ℚ) < (kChiAD box).value.lower := by
    simp only [kChiAD, mulNonnegativeAD,
      RationalEnclosure.mulNonnegative]
    exact mul_pos hkStrict hchiStrict
  have hhK := idealHAD_sound terms hkStrict hvalid.hK hk
  have hhKChi := idealHAD_sound terms hkChiStrict hvalid.hKChi hkChi
  have hqChi := idealQChiAD_sound terms hchiStrict hvalid.qChi hchi
  constructor
  · simpa [evaluatePrimitives] using hhK
  constructor
  · simpa using hhKChi
  · simpa [evaluatePrimitives] using hqChi

/-! ## First complete shared output: `Lambda/2` -/

def d0AD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.mul (IntervalAD.const (1 / 2))
      (IntervalAD.log terms payload.logDArg (dArgAD box)))
    (IntervalAD.invPositive (fourKPlusThreeAD box))

def aAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.divPositive
    (IntervalAD.add
      (IntervalAD.mul (chiAD box)
        (IntervalAD.log terms payload.logOnePlusKChi
          (onePlusKChiAD box)))
      (IntervalAD.log terms payload.logOnePlusK (onePlusKAD box)))
    (onePlusChiAD box)

def sAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.add
      (IntervalAD.log terms payload.logK (kAD box))
      (evaluatePrimitives terms box payload).qChi)
    (aAD terms box payload)

def lambdaHalfAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.mul (IntervalAD.const (1 / 2))
    (IntervalAD.add
      (IntervalAD.add
        (IntervalAD.mul (IntervalAD.const 2)
          (d0AD terms box payload))
        (sAD terms box payload))
      (IntervalAD.const (1 / 3)))

theorem lambdaHalfAD_value_sound
    (terms : ℕ) {box : CertificateBox} {payload : Payload}
    (hvalid : payload.Valid box)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    (lambdaHalfAD terms box payload).value.Contains
      (lrDeterminantIdealLambda point.k point.chi / 2) := by
  have hk : (kAD box).Contains point.k 0 1 0 :=
    IntervalAD.contains_variableK
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  have hchi : (chiAD box).Contains point.chi 0 0 1 :=
    IntervalAD.contains_variableChi
      ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩
  have hkLower : (0 : ℚ) ≤ (kAD box).value.lower := by
    simpa [kAD, CertificateBox.kInterval] using hvalid.domain.1.le
  have hchiLower : (0 : ℚ) ≤ (chiAD box).value.lower := by
    simpa [chiAD, CertificateBox.chiInterval] using hvalid.domain.2.2.1.le
  have hkChi := mulNonnegativeAD_sound hkLower hchiLower hk hchi
  have honeK := IntervalAD.contains_add (IntervalAD.contains_const 1) hk
  have honeKChi := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hkChi
  have honeChi := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hchi
  have htwoK := mulNonnegativeAD_sound
    (by norm_num [IntervalAD.const, RationalEnclosure.point])
    hkLower (IntervalAD.contains_const 2) hk
  have hinvTwoK := IntervalAD.contains_invPositive
    hvalid.denominators.2.1 htwoK
  have hdArg := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hinvTwoK
  have hfourK := mulNonnegativeAD_sound
    (by norm_num [IntervalAD.const, RationalEnclosure.point])
    hkLower (IntervalAD.contains_const 4) hk
  have hfourKThree := IntervalAD.contains_add hfourK
    (IntervalAD.contains_const 3)
  have hlogK := IntervalAD.contains_log terms hvalid.logK hk
  have hlogOnePlusK := IntervalAD.contains_log terms
    hvalid.logOnePlusK honeK
  have hlogOnePlusKChi := IntervalAD.contains_log terms
    hvalid.logOnePlusKChi honeKChi
  have hlogDArg := IntervalAD.contains_log terms hvalid.logDArg hdArg
  have hA := IntervalAD.contains_divPositive hvalid.denominators.1
    (IntervalAD.contains_add
      (IntervalAD.contains_mul hchi hlogOnePlusKChi)
      hlogOnePlusK) honeChi
  have hD := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2))
      hlogDArg)
    (IntervalAD.contains_invPositive hvalid.denominators.2.2
      hfourKThree)
  have hq := (evaluatePrimitives_sound terms hvalid hpoint).2.2
  have hS := IntervalAD.contains_sub
    (IntervalAD.contains_add hlogK hq) hA
  have hraw := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 2))
    (IntervalAD.contains_add
      (IntervalAD.contains_add
        (IntervalAD.contains_mul (IntervalAD.contains_const 2) hD) hS)
      (IntervalAD.contains_const (1 / 3)))
  have hvalue := hraw.1
  convert hvalue using 1
  unfold lrDeterminantIdealLambda lrDeterminantIdealD0
    lrDeterminantIdealS lrDeterminantIdealA
  norm_num [div_eq_mul_inv, mul_inv_rev]
  ring

/-! ## Full parameterized shared graph -/

def logTwoAD (terms : ℕ) (payload : Payload) : IntervalAD :=
  IntervalAD.log terms payload.logTwo (IntervalAD.const 2)

def logFourThirdAD (terms : ℕ) (payload : Payload) : IntervalAD :=
  IntervalAD.log terms payload.logFourThird (IntervalAD.const (4 / 3))

def l0AD (terms : ℕ) (config : Config) (payload : Payload) : IntervalAD :=
  IntervalAD.mul (IntervalAD.const config.l0Scale)
    (logTwoAD terms payload)

def cAD (terms : ℕ) (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.sub (IntervalAD.const 1)
      (IntervalAD.mul (IntervalAD.const 2) (logTwoAD terms payload)))
    (IntervalAD.mul (IntervalAD.const 16)
      (logFourThirdAD terms payload))

def uAD (terms : ℕ) (config : Config) (payload : Payload) : IntervalAD :=
  IntervalAD.add (l0AD terms config payload) (cAD terms payload)

def uSquareAD (terms : ℕ) (config : Config)
    (payload : Payload) : IntervalAD :=
  mulNonnegativeAD (uAD terms config payload) (uAD terms config payload)

def ahAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let primitive := evaluatePrimitives terms box payload
  IntervalAD.divPositive
    (IntervalAD.add
      (IntervalAD.mul (chiAD box) primitive.hKChi) primitive.hK)
    (onePlusChiAD box)

def bConstAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub (logTwoAD terms payload)
    (IntervalAD.mul (IntervalAD.const (1 / 2))
      (IntervalAD.log terms payload.logOnePlusK (onePlusKAD box)))

def p0AD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.add
      (IntervalAD.mul (IntervalAD.const 2) (logTwoAD terms payload))
      (IntervalAD.const 1))
    (aAD terms box payload)

def t0AD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.add
      (IntervalAD.mul (IntervalAD.const 2) (logTwoAD terms payload))
      (IntervalAD.const 1))
    (ahAD terms box payload)

def rInfAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let d := d0AD terms box payload
  let b := bConstAD terms box payload
  let p := p0AD terms box payload
  let s := sAD terms box payload
  let t := t0AD terms box payload
  let c := cAD terms payload
  IntervalAD.add
    (IntervalAD.add
      (IntervalAD.mul d p) (IntervalAD.mul b s))
    (IntervalAD.add
      (IntervalAD.mul (IntervalAD.const (1 / 6))
        (IntervalAD.sub t c))
      (IntervalAD.mul (IntervalAD.const (1 / 3))
        (IntervalAD.sub b d)))

def c1AD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let tMinusC := IntervalAD.sub
    (t0AD terms box payload) (cAD terms payload)
  let second := IntervalAD.sub
    (IntervalAD.sub (bConstAD terms box payload)
      (d0AD terms box payload))
    (IntervalAD.mul (IntervalAD.const (1 / 2))
      (cAD terms payload))
  IntervalAD.mul (IntervalAD.const (1 / 3))
    (IntervalAD.mul tMinusC second)

/-- `F₀` in its separated form.  This is algebraically the current ideal
core at `config.l0` and avoids introducing a second evaluator graph. -/
def f0AD (terms : ℕ) (config : Config) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add
      (IntervalAD.mul (l0AD terms config payload)
        (lambdaHalfAD terms box payload))
      (rInfAD terms box payload))
    (IntervalAD.divPositive (c1AD terms box payload)
      (uAD terms config payload))

structure TargetADTriple where
  first : IntervalAD
  second : IntervalAD
  third : IntervalAD

/-- The exact target transform used by both certificate families.

* `globalTail`: `(F₀-C₁/U-margin, Lambda/2, C₁)`;
* `endpoint`: `(F₀-margin, Lambda/2-C₁/U², C₁)`.
-/
def evaluateTargets (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) : TargetADTriple :=
  let f0 := f0AD terms config box payload
  let lambdaHalf := lambdaHalfAD terms box payload
  let c1 := c1AD terms box payload
  let u := uAD terms config payload
  let margin := IntervalAD.const config.margin
  match config.mode with
  | .globalTail =>
      { first := IntervalAD.sub
          (IntervalAD.sub f0 (IntervalAD.divPositive c1 u)) margin
        second := lambdaHalf
        third := c1 }
  | .endpoint =>
      { first := IntervalAD.sub f0 margin
        second := IntervalAD.sub lambdaHalf
          (IntervalAD.divPositive c1
            (uSquareAD terms config payload))
        third := c1 }

/-- The only new checked denominator introduced by `l0Scale` and target
mode.  Every other side condition is already in `Payload.Valid`. -/
def fullPayloadCheck (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) : Bool :=
  payload.payloadCheck box &&
    decide ((0 : ℚ) < (uAD terms config payload).value.lower)

structure FullValid (terms : ℕ) (config : Config)
    (box : CertificateBox) (payload : Payload) : Prop where
  payloadValid : payload.Valid box
  uPositive : (0 : ℚ) < (uAD terms config payload).value.lower

theorem fullValid_of_check
    {terms : ℕ} {config : Config} {box : CertificateBox}
    {payload : Payload}
    (hcheck : fullPayloadCheck terms config box payload = true) :
    FullValid terms config box payload := by
  have hparts : payload.payloadCheck box = true ∧
      (0 : ℚ) < (uAD terms config payload).value.lower := by
    simpa [fullPayloadCheck] using hcheck
  exact ⟨Payload.valid_of_payloadCheck hparts.1, hparts.2⟩

/-! ### Exact real targets represented by the graph -/

noncomputable def targetFirst (config : Config)
    (point : CertificatePoint) : ℝ :=
  match config.mode with
  | .globalTail =>
      (lrDeterminantIdealCore config.l0 point.k point.chi -
        lrDeterminantIdealC1 point.k point.chi /
          (config.l0 + lrDeterminantIdealC)) - config.margin
  | .endpoint =>
      lrDeterminantIdealCore config.l0 point.k point.chi - config.margin

noncomputable def targetSecond (config : Config)
    (point : CertificatePoint) : ℝ :=
  match config.mode with
  | .globalTail => lrDeterminantIdealLambda point.k point.chi / 2
  | .endpoint =>
      lrDeterminantIdealLDerivative config.l0 point.k point.chi

noncomputable def targetThird (_config : Config)
    (point : CertificatePoint) : ℝ :=
  lrDeterminantIdealC1 point.k point.chi

/-- Syntactic invariant used by the midpoint adapter: none of the shared
outputs depends on the dummy `s` coordinate, and the AD graph initializes
only `k` and `chi` as variables. -/
theorem targetFirst_update_s (config : Config)
    (point : CertificatePoint) (s : ℝ) :
    targetFirst config { point with s := s } = targetFirst config point := by
  cases config.mode <;> rfl

theorem targetSecond_update_s (config : Config)
    (point : CertificatePoint) (s : ℝ) :
    targetSecond config { point with s := s } = targetSecond config point := by
  cases config.mode <;> rfl

theorem targetThird_update_s (config : Config)
    (point : CertificatePoint) (s : ℝ) :
    targetThird config { point with s := s } = targetThird config point := by
  rfl

end LRLowKIdealSharedPrimitiveAD
end CourtadeKumar
