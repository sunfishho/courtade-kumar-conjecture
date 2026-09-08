import InformationTheory.CourtadeKumar.LRHighShapeCoordinateAD
import InformationTheory.CourtadeKumar.LRSmallSBridgeFrozenCore

/-!
# Semantic interval expression for the frozen small-`s` core

This module contains the arithmetic evaluator, its proof-carrying payload,
and the semantic soundness theorems needed by compact replay (M30).  It has no
payload generator or subdivision-tree interface, so semantic clients need not
import the substantially larger auto-generation dependency graph.  Boxes
touching `chi = 0` use the verified direct endpoint enclosure.
-/

namespace CourtadeKumar

noncomputable def lrSmallSBridgeCoreB (point : CertificatePoint) : ℝ :=
  Real.log (1 + lrCertificateV point) -
    Real.log (1 + (1 - point.s) * point.k) / 2

noncomputable def lrSmallSBridgeCoreTarget
    (point : CertificatePoint) : ℝ :=
  let L := 14 * Real.log 2
  let B := L / 2 + lrSmallSBridgeCoreB point
  let D := lrSmallSBridgeD point.s point.k
  let p := lrSmallSBridgeP point.s point.k point.chi L
  let S := Real.log point.k + lrSmallSBridgeQChi point.chi - point.s -
    lrSmallSBridgeAR point.s point.k point.chi
  point.k * (1 + point.chi) / 4 * (D * p + B * S) + (B - D) / 4

theorem lrSmallSBridgeCoreTarget_eq_frozen (point : CertificatePoint) :
    lrSmallSBridgeCoreTarget point =
      lrSmallSBridgeFrozen point.s point.k point.chi
        (14 * Real.log 2) (lrSmallSBridgeCoreB point) := by
  unfold lrSmallSBridgeCoreTarget lrSmallSBridgeFrozen
  rw [lrSmallSBridgeS_eq]
  ring

structure LRSmallSBridgeCoreCertificate where
  coordinate : LRHighShapeCoordinateCertificate
  logTwo : RationalEnclosure.LogIntervalCertificate
  logInner : RationalEnclosure.LogIntervalCertificate
  logOuter : RationalEnclosure.LogIntervalCertificate
  logK : RationalEnclosure.LogIntervalCertificate
  logChi : RationalEnclosure.LogIntervalCertificate
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logDArg : RationalEnclosure.LogIntervalCertificate

namespace LRSmallSBridgeCoreCertificate

def sAD (box : CertificateBox) : IntervalAD := lrCertificateSAD box
def kAD (box : CertificateBox) : IntervalAD := lrCertificateKAD box
def chiAD (box : CertificateBox) : IntervalAD := lrCertificateChiAD box

def rAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.sub (IntervalAD.const 1) (sAD box)

def outerAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1)
    (IntervalAD.mul (rAD box) (kAD box))

def innerAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1)
    (IntervalAD.mul (IntervalAD.mul (rAD box) (kAD box)) (chiAD box))

def onePlusChiAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) (chiAD box)

def dArgAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.divPositive (outerAD box) (kAD box)

def qChiEndpointRawAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : IntervalAD :=
  let hi := IntervalAD.const box.chiHi
  if box.chiHi = 0 then IntervalAD.const 0
  else IntervalAD.divPositive
    (IntervalAD.mul hi (IntervalAD.log terms certificate.logChi hi))
    (IntervalAD.add (IntervalAD.const 1) hi)

def qChiEndpointAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : IntervalAD where
  value := ⟨(qChiEndpointRawAD terms box certificate).value.lower, 0⟩
  derivS := RationalEnclosure.point 0
  derivK := RationalEnclosure.point 0
  derivChi := RationalEnclosure.point 0

def qChiAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : IntervalAD :=
  if box.chiLo = 0 then qChiEndpointAD terms box certificate
  else
    IntervalAD.divPositive
      (IntervalAD.mul (chiAD box)
        (IntervalAD.log terms certificate.logChi (chiAD box)))
      (onePlusChiAD box)

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : IntervalAD :=
  let s := sAD box
  let k := kAD box
  let chi := chiAD box
  let v := certificate.coordinate.vAD box
  let logTwo := IntervalAD.log terms certificate.logTwo (IntervalAD.const 2)
  let logInner := IntervalAD.log terms certificate.logInner (innerAD box)
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

def payloadCheck (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : Bool :=
  certificate.coordinate.check box &&
    decide ((0 : ℚ) ≤ box.sLo ∧ box.sHi ≤ 1 / 16384 ∧
      1 / 4 ≤ box.kLo ∧ box.kHi ≤ 4 ∧
      0 ≤ box.chiLo ∧ box.chiHi ≤ 1) &&
    decide ((0 : ℚ) < (kAD box).value.lower) &&
    decide ((0 : ℚ) < (onePlusChiAD box).value.lower) &&
    certificate.logTwo.check (IntervalAD.const 2).value &&
    certificate.logInner.check (innerAD box).value &&
    certificate.logOuter.check (outerAD box).value &&
    certificate.logK.check (kAD box).value &&
    (if box.chiLo = 0 then
      if box.chiHi = 0 then true
      else decide (box.chiHi ≤ 1 / 4) &&
        certificate.logChi.check (IntervalAD.const box.chiHi).value
      else certificate.logChi.check (chiAD box).value) &&
    certificate.logOnePlusV.check
      (IntervalAD.add (IntervalAD.const 1)
        (certificate.coordinate.vAD box)).value &&
    certificate.logDArg.check (dArgAD box).value

def check (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : Bool :=
  payloadCheck box certificate &&
    decide ((2 / 3 : ℚ) < (certificate.evaluate terms box).value.lower)

structure Valid (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : Prop where
  coordinate : certificate.coordinate.check box = true
  domain : (0 : ℚ) ≤ box.sLo ∧ box.sHi ≤ 1 / 16384 ∧
    1 / 4 ≤ box.kLo ∧ box.kHi ≤ 4 ∧
    0 ≤ box.chiLo ∧ box.chiHi ≤ 1
  kPositive : (0 : ℚ) < (kAD box).value.lower
  onePlusChiPositive : (0 : ℚ) < (onePlusChiAD box).value.lower
  logTwo : certificate.logTwo.check (IntervalAD.const 2).value = true
  logInner : certificate.logInner.check (innerAD box).value = true
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

theorem valid_of_payloadCheck
    {box : CertificateBox} {certificate : LRSmallSBridgeCoreCertificate}
    (hcheck : payloadCheck box certificate = true) :
    Valid box certificate := by
  have h :
      certificate.coordinate.check box = true ∧
      ((0 : ℚ) ≤ box.sLo ∧ box.sHi ≤ 1 / 16384 ∧
        1 / 4 ≤ box.kLo ∧ box.kHi ≤ 4 ∧
        0 ≤ box.chiLo ∧ box.chiHi ≤ 1) ∧
      (0 : ℚ) < (kAD box).value.lower ∧
      (0 : ℚ) < (onePlusChiAD box).value.lower ∧
      certificate.logTwo.check (IntervalAD.const 2).value = true ∧
      certificate.logInner.check (innerAD box).value = true ∧
      certificate.logOuter.check (outerAD box).value = true ∧
      certificate.logK.check (kAD box).value = true ∧
      (if box.chiLo = 0 then
        if box.chiHi = 0 then true
        else decide (box.chiHi ≤ 1 / 4) &&
          certificate.logChi.check (IntervalAD.const box.chiHi).value
        else certificate.logChi.check (chiAD box).value) = true ∧
      certificate.logOnePlusV.check
        (IntervalAD.add (IntervalAD.const 1)
          (certificate.coordinate.vAD box)).value = true ∧
      certificate.logDArg.check (dArgAD box).value = true := by
    simpa [payloadCheck, and_assoc] using hcheck
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

theorem qChiAD_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate}
    (hpoint : box.Contains point) (hvalid : Valid box certificate) :
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
        simpa [hz, hhi] using hvalid.logChi
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
      simpa [hz] using hvalid.logChi
    have hlog := IntervalAD.contains_log terms hlogCheck hchiAD
    have hone := IntervalAD.contains_add (IntervalAD.contains_const 1) hchiAD
    have hq := IntervalAD.contains_divPositive hvalid.onePlusChiPositive
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

theorem evaluate_value_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate}
    (hpoint : box.Contains point) (hvalid : Valid box certificate) :
    (certificate.evaluate terms box).value.Contains
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
  have hlogInner := IntervalAD.contains_log terms hvalid.logInner hinner
  have hlogOuter := IntervalAD.contains_log terms hvalid.logOuter houter
  have hlogK := IntervalAD.contains_log terms hvalid.logK hk
  have hlogOnePlusV := IntervalAD.contains_log terms hvalid.logOnePlusV honeV
  have hlogDArg := IntervalAD.contains_log terms hvalid.logDArg hdArg
  rcases qChiAD_sound terms hpoint hvalid with ⟨qS, qK, qC, hq⟩
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
  simpa [evaluate, lrSmallSBridgeCoreTarget, lrSmallSBridgeCoreB,
    lrSmallSBridgeD, lrSmallSBridgeP, lrSmallSBridgeAR] using hvalue

theorem positive_of_check
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.check terms box = true) :
    (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point := by
  have hparts := Bool.and_eq_true_iff.mp
    (by simpa [check] using hcheck)
  have hvalid := valid_of_payloadCheck hparts.1
  have hlowerRat : (2 / 3 : ℚ) <
      (certificate.evaluate terms box).value.lower := by
    simpa using hparts.2
  have hlowerReal : (2 / 3 : ℝ) <
      ((certificate.evaluate terms box).value.lower : ℝ) := by
    have hcast : (((2 / 3 : ℚ) : ℚ) : ℝ) <
        ((certificate.evaluate terms box).value.lower : ℝ) := by
      exact_mod_cast hlowerRat
    norm_num at hcast ⊢
    exact hcast
  exact hlowerReal.trans_le (evaluate_value_sound terms hpoint hvalid).1

end LRSmallSBridgeCoreCertificate

end CourtadeKumar

