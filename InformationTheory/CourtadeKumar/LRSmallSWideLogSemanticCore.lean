import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreIntervalCore

/-!
# Additive wide-log semantics for the small-s bridge

The historical evaluator is unchanged.  This sibling evaluator replaces only
its `logInner` node by independently authenticated endpoint bounds, while the
reciprocal slope continues to use the exact leaf input interval.
-/

namespace CourtadeKumar
namespace LRSmallSWideLog

open LRSmallSBridgeCoreCertificate

structure EndpointCache where
  input : ℚ
  certificate : RationalEnclosure.LogRangeCertificate
  enclosure : RationalEnclosure

structure EndpointCache.Valid (terms : ℕ) (cache : EndpointCache) : Prop where
  check : cache.certificate.check cache.input = true
  binding : cache.enclosure = cache.certificate.enclosure terms

theorem EndpointCache.sound {terms : ℕ} {cache : EndpointCache}
    (hvalid : cache.Valid terms) :
    cache.enclosure.Contains (Real.log (cache.input : ℝ)) := by
  rw [hvalid.binding]
  exact cache.certificate.sound terms hvalid.check

structure WideLogData where
  lower : EndpointCache
  upper : EndpointCache

def WideLogData.output (data : WideLogData) : RationalEnclosure :=
  ⟨data.lower.enclosure.lower, data.upper.enclosure.upper⟩

def wideLog (data : WideLogData) (a : IntervalAD) : IntervalAD :=
  IntervalAD.unary data.output
    (RationalEnclosure.invPositive a.value) a

structure WideLogData.Valid (terms : ℕ) (a : IntervalAD)
    (data : WideLogData) : Prop where
  lower : data.lower.Valid terms
  upper : data.upper.Valid terms
  lowerPositive : (0 : ℚ) < data.lower.input
  lowerCovers : data.lower.input ≤ a.value.lower
  upperCovers : a.value.upper ≤ data.upper.input

/-- The certificate obligations used by `evaluateWide`.  This deliberately
omits the historical `logInner` check: the inner logarithm is justified by
`WideLogData.Valid` instead. -/
structure WideCertificateValid (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : Prop where
  coordinate : certificate.coordinate.check box = true
  domain : (0 : ℚ) ≤ box.sLo ∧ box.sHi ≤ 1 / 16384 ∧
    1 / 4 ≤ box.kLo ∧ box.kHi ≤ 4 ∧
    0 ≤ box.chiLo ∧ box.chiHi ≤ 1
  kPositive : (0 : ℚ) < (kAD box).value.lower
  onePlusChiPositive : (0 : ℚ) < (onePlusChiAD box).value.lower
  logTwo : certificate.logTwo.check (IntervalAD.const 2).value = true
  logOuter : certificate.logOuter.check (outerAD box).value = true
  logK : certificate.logK.check (kAD box).value = true
  logChi : (if box.chiLo = 0 then
    if box.chiHi = 0 then true
    else decide (box.chiHi ≤ 1 / 4) &&
      certificate.logChi.check (IntervalAD.const box.chiHi).value
    else certificate.logChi.check (chiAD box).value) = true
  logOnePlusV : certificate.logOnePlusV.check
    (IntervalAD.add (IntervalAD.const 1)
      (certificate.coordinate.vAD box)).value = true
  logDArg : certificate.logDArg.check (dArgAD box).value = true

theorem contains_wideLog (terms : ℕ) {data : WideLogData}
    {a : IntervalAD} {av as ak ac : ℝ}
    (hvalid : data.Valid terms a)
    (ha : a.Contains av as ak ac) :
    (wideLog data a).Contains (Real.log av)
      (as / av) (ak / av) (ac / av) := by
  have hloCast : (data.lower.input : ℝ) ≤ (a.value.lower : ℝ) := by
    exact_mod_cast hvalid.lowerCovers
  have hhiCast : (a.value.upper : ℝ) ≤ (data.upper.input : ℝ) := by
    exact_mod_cast hvalid.upperCovers
  have hloPos : (0 : ℝ) < (data.lower.input : ℝ) := by
    exact_mod_cast hvalid.lowerPositive
  have havLower : (data.lower.input : ℝ) ≤ av :=
    hloCast.trans ha.1.1
  have havUpper : av ≤ (data.upper.input : ℝ) :=
    ha.1.2.trans hhiCast
  have havPos : 0 < av := hloPos.trans_le havLower
  have hlogLower : Real.log (data.lower.input : ℝ) ≤ Real.log av :=
    Real.log_le_log hloPos havLower
  have hlogUpper : Real.log av ≤ Real.log (data.upper.input : ℝ) :=
    Real.log_le_log havPos havUpper
  have hout : data.output.Contains (Real.log av) :=
    ⟨(EndpointCache.sound hvalid.lower).1.trans hlogLower,
      hlogUpper.trans (EndpointCache.sound hvalid.upper).2⟩
  have hleafPositive : (0 : ℚ) < a.value.lower :=
    hvalid.lowerPositive.trans_le hvalid.lowerCovers
  have hslope := RationalEnclosure.contains_invPositive hleafPositive ha.1
  have hresult := IntervalAD.contains_unary hout hslope ha
  simpa [wideLog, div_eq_mul_inv, mul_comm] using hresult

def evaluateWide (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate)
    (innerLog : WideLogData) : IntervalAD :=
  let s := sAD box
  let k := kAD box
  let chi := chiAD box
  let v := certificate.coordinate.vAD box
  let logTwo := IntervalAD.log terms certificate.logTwo (IntervalAD.const 2)
  let logInner := wideLog innerLog (innerAD box)
  let logOuter := IntervalAD.log terms certificate.logOuter (outerAD box)
  let logK := IntervalAD.log terms certificate.logK k
  let logOnePlusV := IntervalAD.log terms certificate.logOnePlusV
    (IntervalAD.add (IntervalAD.const 1) v)
  let logDArg := IntervalAD.log terms certificate.logDArg (dArgAD box)
  let qchi := qChiAD terms box certificate
  let A := IntervalAD.divPositive
    (IntervalAD.add (IntervalAD.mul chi logInner) logOuter)
    (onePlusChiAD box)
  let L := IntervalAD.mul (IntervalAD.const 14) logTwo
  let p := IntervalAD.sub
    (IntervalAD.sub
      (IntervalAD.add
        (IntervalAD.add L (IntervalAD.mul (IntervalAD.const 2) logTwo))
        (IntervalAD.const 1)) s) A
  let S := IntervalAD.sub
    (IntervalAD.sub (IntervalAD.add logK qchi) s) A
  let b := IntervalAD.sub logOnePlusV
    (IntervalAD.divPositive logOuter (IntervalAD.const 2))
  let B := IntervalAD.add
    (IntervalAD.divPositive L (IntervalAD.const 2)) b
  let D := IntervalAD.divPositive logDArg (IntervalAD.const 2)
  IntervalAD.add
    (IntervalAD.mul
      (IntervalAD.divPositive
        (IntervalAD.mul k (IntervalAD.add (IntervalAD.const 1) chi))
        (IntervalAD.const 4))
      (IntervalAD.add (IntervalAD.mul D p) (IntervalAD.mul B S)))
    (IntervalAD.divPositive (IntervalAD.sub B D) (IntervalAD.const 4))

/-- Soundness of the shared `qChiAD` circuit under precisely the two
certificate obligations it consumes. -/
theorem qChiAD_sound_of_logChi
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate}
    (hpoint : box.Contains point)
    (hlogChi : (if box.chiLo = 0 then
      if box.chiHi = 0 then true
      else decide (box.chiHi ≤ 1 / 4) &&
        certificate.logChi.check (IntervalAD.const box.chiHi).value
      else certificate.logChi.check (chiAD box).value) = true)
    (honePlusChiPositive :
      (0 : ℚ) < (onePlusChiAD box).value.lower) :
    ∃ ds dk dchi : ℝ,
      (qChiAD terms box certificate).Contains
        (lrSmallSBridgeQChi point.chi) ds dk dchi := by
  have hchiAD : (chiAD box).Contains point.chi 0 0 1 := by
    exact IntervalAD.contains_variableChi
      (show box.chiInterval.Contains point.chi from
        ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)
  by_cases hz : box.chiLo = 0
  · have hlo : (0 : ℝ) ≤ point.chi := by
      have := hpoint.2.2.2.2.1
      rw [hz] at this
      exact_mod_cast this
    have hzero : (RationalEnclosure.point (0 : ℚ)).Contains (0 : ℝ) :=
      by norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    by_cases hhi : box.chiHi = 0
    · have hpointZero : point.chi = 0 := by
        have hup := hpoint.2.2.2.2.2
        rw [hhi] at hup
        norm_num at hup
        linarith
      refine ⟨0, 0, 0, ?_⟩
      simp [qChiAD, hz, qChiEndpointAD, qChiEndpointRawAD,
        hhi, hpointZero, lrSmallSBridgeQChi, IntervalAD.Contains,
        IntervalAD.const, RationalEnclosure.Contains, RationalEnclosure.point]
    · have hlogParts : box.chiHi ≤ (1 / 4 : ℚ) ∧
          certificate.logChi.check (IntervalAD.const box.chiHi).value = true := by
        simpa [hz, hhi] using hlogChi
      have hhiNonnegReal : (0 : ℝ) ≤ (box.chiHi : ℝ) :=
        hlo.trans hpoint.2.2.2.2.2
      have hhiNonneg : (0 : ℚ) ≤ box.chiHi := by exact_mod_cast hhiNonnegReal
      have hhiAD := IntervalAD.contains_const box.chiHi
      have hlogHi := IntervalAD.contains_log terms hlogParts.2 hhiAD
      have honeHi := IntervalAD.contains_add (IntervalAD.contains_const 1) hhiAD
      have hden : (0 : ℚ) <
          (IntervalAD.add (IntervalAD.const 1)
            (IntervalAD.const box.chiHi)).value.lower := by
        norm_num [IntervalAD.add, IntervalAD.const, RationalEnclosure.add,
          RationalEnclosure.point, RationalEnclosure.center,
          RationalEnclosure.radius]
        linarith
      have hraw := IntervalAD.contains_divPositive hden
        (IntervalAD.contains_mul hhiAD hlogHi) honeHi
      have hrawValue :
          (qChiEndpointRawAD terms box certificate).value.Contains
            (lrSmallSBridgeQChi (box.chiHi : ℝ)) := by
        have := hraw.1
        simpa [qChiEndpointRawAD, hhi, lrSmallSBridgeQChi] using this
      have hhiMem : (box.chiHi : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 4) :=
        ⟨hhiNonnegReal, by
          have hcast : ((box.chiHi : ℚ) : ℝ) ≤ (((1 / 4 : ℚ) : ℚ) : ℝ) := by
            exact_mod_cast hlogParts.1
          norm_num at hcast ⊢
          exact hcast⟩
      have hpointMem : point.chi ∈ Set.Icc (0 : ℝ) (1 / 4) :=
        ⟨hlo, hpoint.2.2.2.2.2.trans hhiMem.2⟩
      have hqOrder := lrSmallSBridgeQChi_antitoneOn_quarter
        hpointMem hhiMem hpoint.2.2.2.2.2
      have hqNonpos := lrSmallSBridgeQChi_nonpos
        ⟨hlo, hpointMem.2.trans (by norm_num)⟩
      have hqValue :
          (qChiEndpointAD terms box certificate).value.Contains
            (lrSmallSBridgeQChi point.chi) := by
        have hbounds :
            ((qChiEndpointRawAD terms box certificate).value.lower : ℝ) ≤
                lrSmallSBridgeQChi point.chi ∧
              lrSmallSBridgeQChi point.chi ≤ 0 :=
          ⟨hrawValue.1.trans hqOrder, hqNonpos⟩
        simpa [qChiEndpointAD, RationalEnclosure.Contains] using hbounds
      refine ⟨0, 0, 0, ?_⟩
      simp only [qChiAD, hz, if_pos, IntervalAD.Contains]
      exact ⟨hqValue, hzero, hzero, hzero⟩
  · have hlogCheck :
        certificate.logChi.check (chiAD box).value = true := by
      simpa [hz] using hlogChi
    have hlog := IntervalAD.contains_log terms hlogCheck hchiAD
    have hone := IntervalAD.contains_add (IntervalAD.contains_const 1) hchiAD
    have hq := IntervalAD.contains_divPositive honePlusChiPositive
      (IntervalAD.contains_mul hchiAD hlog) hone
    let ds : ℝ :=
      ((0 * Real.log point.chi + point.chi * (0 / point.chi)) *
          (1 + point.chi) - point.chi * Real.log point.chi * (0 + 0)) /
        (1 + point.chi) ^ 2
    let dchi : ℝ :=
      ((1 * Real.log point.chi + point.chi * (1 / point.chi)) *
          (1 + point.chi) - point.chi * Real.log point.chi * (0 + 1)) /
        (1 + point.chi) ^ 2
    refine ⟨ds, ds, dchi, ?_⟩
    simpa [qChiAD, hz, lrSmallSBridgeQChi, ds, dchi] using hq

theorem evaluateWide_value_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate} {innerLog : WideLogData}
    (hpoint : box.Contains point)
    (hvalid : WideCertificateValid box certificate)
    (hinnerValid : innerLog.Valid terms (innerAD box)) :
    (evaluateWide terms box certificate innerLog).value.Contains
      (lrSmallSBridgeCoreTarget point) := by
  have hs : (sAD box).Contains point.s 1 0 0 := by
    exact IntervalAD.contains_variableS
      (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hk : (kAD box).Contains point.k 0 1 0 := by
    exact IntervalAD.contains_variableK
      (show box.kInterval.Contains point.k from
        ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  have hchi : (chiAD box).Contains point.chi 0 0 1 := by
    exact IntervalAD.contains_variableChi
      (show box.chiInterval.Contains point.chi from
        ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)
  have hr := IntervalAD.contains_sub (IntervalAD.contains_const 1) hs
  have houter := IntervalAD.contains_add (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul hr hk)
  have hinner := IntervalAD.contains_add (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul (IntervalAD.contains_mul hr hk) hchi)
  have honeChi := IntervalAD.contains_add (IntervalAD.contains_const 1) hchi
  have hv := certificate.coordinate.vAD_sound hpoint hvalid.coordinate
  have honeV := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have hdArg := IntervalAD.contains_divPositive hvalid.kPositive houter hk
  have hlogTwo := IntervalAD.contains_log terms hvalid.logTwo
    (IntervalAD.contains_const 2)
  have hlogInner := contains_wideLog terms hinnerValid hinner
  have hlogOuter := IntervalAD.contains_log terms hvalid.logOuter houter
  have hlogK := IntervalAD.contains_log terms hvalid.logK hk
  have hlogOnePlusV := IntervalAD.contains_log terms hvalid.logOnePlusV honeV
  have hlogDArg := IntervalAD.contains_log terms hvalid.logDArg hdArg
  rcases qChiAD_sound_of_logChi terms hpoint hvalid.logChi
      hvalid.onePlusChiPositive with ⟨qS, qK, qC, hq⟩
  have hA := IntervalAD.contains_divPositive hvalid.onePlusChiPositive
    (IntervalAD.contains_add (IntervalAD.contains_mul hchi hlogInner) hlogOuter)
    honeChi
  have hL := IntervalAD.contains_mul (IntervalAD.contains_const 14) hlogTwo
  have hp := IntervalAD.contains_sub
    (IntervalAD.contains_sub
      (IntervalAD.contains_add
        (IntervalAD.contains_add hL
          (IntervalAD.contains_mul (IntervalAD.contains_const 2) hlogTwo))
        (IntervalAD.contains_const 1)) hs) hA
  have hS := IntervalAD.contains_sub
    (IntervalAD.contains_sub (IntervalAD.contains_add hlogK hq) hs) hA
  have htwoPositive : (0 : ℚ) < (IntervalAD.const 2).value.lower := by
    norm_num [IntervalAD.const, RationalEnclosure.point]
  have hfourPositive : (0 : ℚ) < (IntervalAD.const 4).value.lower := by
    norm_num [IntervalAD.const, RationalEnclosure.point]
  have hb := IntervalAD.contains_sub hlogOnePlusV
    (IntervalAD.contains_divPositive htwoPositive
      hlogOuter (IntervalAD.contains_const 2))
  have hB := IntervalAD.contains_add
    (IntervalAD.contains_divPositive htwoPositive
      hL (IntervalAD.contains_const 2)) hb
  have hD := IntervalAD.contains_divPositive htwoPositive
    hlogDArg (IntervalAD.contains_const 2)
  have hscale := IntervalAD.contains_divPositive hfourPositive
    (IntervalAD.contains_mul hk
      (IntervalAD.contains_add (IntervalAD.contains_const 1) hchi))
    (IntervalAD.contains_const 4)
  have hmain := IntervalAD.contains_mul hscale
    (IntervalAD.contains_add (IntervalAD.contains_mul hD hp)
      (IntervalAD.contains_mul hB hS))
  have htail := IntervalAD.contains_divPositive hfourPositive
    (IntervalAD.contains_sub hB hD) (IntervalAD.contains_const 4)
  have hresult := IntervalAD.contains_add hmain htail
  have hvalue := hresult.1
  simpa [evaluateWide, lrSmallSBridgeCoreTarget, lrSmallSBridgeCoreB,
    lrSmallSBridgeD, lrSmallSBridgeP, lrSmallSBridgeAR] using hvalue

theorem positive_of_evaluateWide
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate} {innerLog : WideLogData}
    (hpoint : box.Contains point)
    (hvalid : WideCertificateValid box certificate)
    (hinnerValid : innerLog.Valid terms (innerAD box))
    (hlower : (2 / 3 : ℚ) <
      (evaluateWide terms box certificate innerLog).value.lower) :
    (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point := by
  have hlowerReal : (2 / 3 : ℝ) <
      ((evaluateWide terms box certificate innerLog).value.lower : ℝ) := by
    have hcast : (((2 / 3 : ℚ) : ℚ) : ℝ) <
        ((evaluateWide terms box certificate innerLog).value.lower : ℝ) := by
      exact_mod_cast hlower
    norm_num at hcast ⊢
    exact hcast
  exact hlowerReal.trans_le
    (evaluateWide_value_sound terms hpoint hvalid hinnerValid).1

end LRSmallSWideLog
end CourtadeKumar
