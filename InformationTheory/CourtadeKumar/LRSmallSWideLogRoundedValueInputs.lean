import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedCore

/-!
# Compact primitive inputs for scalar rounded evaluation

The seven elementary enclosures are authenticated outside the final leaf
reduction.  Consequently the leaf checker evaluates only a short circuit of
small dyadic scalar intervals.
-/

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedValue

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLog
open LRSmallSWideLogRounded

structure Inputs where
  logTwo : RationalEnclosure
  logInner : RationalEnclosure
  logOuter : RationalEnclosure
  logK : RationalEnclosure
  logOnePlusV : RationalEnclosure
  logDArg : RationalEnclosure
  qChi : RationalEnclosure

def evaluate (bits : ℕ) (box : CertificateBox)
    (inputs : Inputs) : RationalEnclosure :=
  let s := (sAD box).value
  let k := (kAD box).value
  let chi := (chiAD box).value
  let A := divPositive bits
    (add bits (mul bits chi inputs.logInner) inputs.logOuter)
    (onePlusChiAD box).value
  let L := mul bits (RationalEnclosure.point 14) inputs.logTwo
  let p := sub bits
    (sub bits
      (add bits
        (add bits L
          (mul bits (RationalEnclosure.point 2) inputs.logTwo))
        (RationalEnclosure.point 1)) s) A
  let S := sub bits
    (sub bits (add bits inputs.logK inputs.qChi) s) A
  let b := sub bits inputs.logOnePlusV
    (divPositive bits inputs.logOuter (RationalEnclosure.point 2))
  let B := add bits (divPositive bits L (RationalEnclosure.point 2)) b
  let D := divPositive bits inputs.logDArg (RationalEnclosure.point 2)
  let scale := divPositive bits
    (mul bits k (add bits (RationalEnclosure.point 1) chi))
    (RationalEnclosure.point 4)
  let mainInner := add bits (mul bits D p) (mul bits B S)
  let main := mul bits scale mainInner
  let tail := divPositive bits (sub bits B D) (RationalEnclosure.point 4)
  add bits main tail

def lowerCheck (bits : ℕ) (box : CertificateBox) (inputs : Inputs) : Bool :=
  decide ((2 / 3 : ℚ) < (evaluate bits box inputs).lower)

structure CoversExact (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate)
    (innerLog : WideLogData) (inputs : Inputs) : Prop where
  logTwo : LRUpperKMidpointCoarsening.Covers inputs.logTwo
    (IntervalAD.log terms certificate.logTwo (IntervalAD.const 2)).value
  logInner : LRUpperKMidpointCoarsening.Covers inputs.logInner
    (wideLog innerLog (innerAD box)).value
  logOuter : LRUpperKMidpointCoarsening.Covers inputs.logOuter
    (IntervalAD.log terms certificate.logOuter (outerAD box)).value
  logK : LRUpperKMidpointCoarsening.Covers inputs.logK
    (IntervalAD.log terms certificate.logK (kAD box)).value
  logOnePlusV : LRUpperKMidpointCoarsening.Covers inputs.logOnePlusV
    (IntervalAD.log terms certificate.logOnePlusV
      (IntervalAD.add (IntervalAD.const 1)
        (certificate.coordinate.vAD box))).value
  logDArg : LRUpperKMidpointCoarsening.Covers inputs.logDArg
    (IntervalAD.log terms certificate.logDArg (dArgAD box)).value
  qChi : LRUpperKMidpointCoarsening.Covers inputs.qChi
    (qChiAD terms box certificate).value

theorem evaluate_sound
    (bits terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate} {innerLog : WideLogData}
    {inputs : Inputs}
    (hpoint : box.Contains point)
    (hvalid : WideCertificateValid box certificate)
    (hinnerValid : innerLog.Valid terms (innerAD box))
    (hcovers : CoversExact terms box certificate innerLog inputs) :
    (evaluate bits box inputs).Contains (lrSmallSBridgeCoreTarget point) := by
  have hs : (sAD box).value.Contains point.s :=
    (IntervalAD.contains_variableS
      (show box.sInterval.Contains point.s from
        ⟨hpoint.1, hpoint.2.1⟩)).1
  have hkAD := IntervalAD.contains_variableK
    (show box.kInterval.Contains point.k from
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  have hk : (kAD box).value.Contains point.k := hkAD.1
  have hchiAD := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains point.chi from
      ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)
  have hchi : (chiAD box).value.Contains point.chi := hchiAD.1
  have hr := IntervalAD.contains_sub (IntervalAD.contains_const 1)
    (IntervalAD.contains_variableS
      (show box.sInterval.Contains point.s from
        ⟨hpoint.1, hpoint.2.1⟩))
  have houter := IntervalAD.contains_add (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul hr hkAD)
  have hinner := IntervalAD.contains_add (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul (IntervalAD.contains_mul hr hkAD) hchiAD)
  have honeChi := IntervalAD.contains_add (IntervalAD.contains_const 1) hchiAD
  have hv := certificate.coordinate.vAD_sound hpoint hvalid.coordinate
  have honeV := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have hdArg := IntervalAD.contains_divPositive hvalid.kPositive houter hkAD
  have hlogTwo := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.logTwo
    (IntervalAD.contains_log terms hvalid.logTwo
      (IntervalAD.contains_const 2)).1
  have hlogInner := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.logInner (contains_wideLog terms hinnerValid hinner).1
  have hlogOuter := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.logOuter
    (IntervalAD.contains_log terms hvalid.logOuter houter).1
  have hlogK := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.logK (IntervalAD.contains_log terms hvalid.logK hkAD).1
  have hlogOnePlusV := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.logOnePlusV
    (IntervalAD.contains_log terms hvalid.logOnePlusV honeV).1
  have hlogDArg := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.logDArg
    (IntervalAD.contains_log terms hvalid.logDArg hdArg).1
  rcases qChiAD_sound_of_logChi terms hpoint hvalid.logChi
      hvalid.onePlusChiPositive with ⟨qS, qK, qC, hqExact⟩
  have hq := LRUpperKMidpointCoarsening.contains_of_covers
    hcovers.qChi hqExact.1
  have hA := contains_divPositive (bits := bits)
    hvalid.onePlusChiPositive
    (contains_add (bits := bits)
      (contains_mul (bits := bits) hchi hlogInner) hlogOuter)
    honeChi.1
  have hL := contains_mul (bits := bits)
    (RationalEnclosure.contains_point 14) hlogTwo
  have hp := contains_sub (bits := bits)
    (contains_sub (bits := bits)
      (contains_add (bits := bits)
        (contains_add (bits := bits) hL
          (contains_mul (bits := bits)
            (RationalEnclosure.contains_point 2) hlogTwo))
        (RationalEnclosure.contains_point 1)) hs) hA
  have hS := contains_sub (bits := bits)
    (contains_sub (bits := bits)
      (contains_add (bits := bits) hlogK hq) hs) hA
  have htwoPositive : (0 : ℚ) < (RationalEnclosure.point 2).lower := by
    norm_num [RationalEnclosure.point]
  have hfourPositive : (0 : ℚ) < (RationalEnclosure.point 4).lower := by
    norm_num [RationalEnclosure.point]
  have hb := contains_sub (bits := bits) hlogOnePlusV
    (contains_divPositive (bits := bits) htwoPositive hlogOuter
      (RationalEnclosure.contains_point 2))
  have hB := contains_add (bits := bits)
    (contains_divPositive (bits := bits) htwoPositive hL
      (RationalEnclosure.contains_point 2)) hb
  have hD := contains_divPositive (bits := bits) htwoPositive
    hlogDArg (RationalEnclosure.contains_point 2)
  have hscale := contains_divPositive (bits := bits) hfourPositive
    (contains_mul (bits := bits) hk
      (contains_add (bits := bits)
        (RationalEnclosure.contains_point 1) hchi))
    (RationalEnclosure.contains_point 4)
  have hmain := contains_mul (bits := bits) hscale
    (contains_add (bits := bits)
      (contains_mul (bits := bits) hD hp)
      (contains_mul (bits := bits) hB hS))
  have htail := contains_divPositive (bits := bits) hfourPositive
    (contains_sub (bits := bits) hB hD)
    (RationalEnclosure.contains_point 4)
  have hresult := contains_add (bits := bits) hmain htail
  simpa [evaluate, lrSmallSBridgeCoreTarget, lrSmallSBridgeCoreB,
    lrSmallSBridgeD, lrSmallSBridgeP, lrSmallSBridgeAR] using hresult

theorem positive_of_lowerCheck
    (bits terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate} {innerLog : WideLogData}
    {inputs : Inputs}
    (hpoint : box.Contains point)
    (hvalid : WideCertificateValid box certificate)
    (hinnerValid : innerLog.Valid terms (innerAD box))
    (hcovers : CoversExact terms box certificate innerLog inputs)
    (hcheck : lowerCheck bits box inputs = true) :
    (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point := by
  have hlower : (2 / 3 : ℚ) < (evaluate bits box inputs).lower := by
    simpa only [lowerCheck, decide_eq_true_eq] using hcheck
  have hlowerReal : (2 / 3 : ℝ) <
      ((evaluate bits box inputs).lower : ℝ) := by
    have hcast : (((2 / 3 : ℚ) : ℚ) : ℝ) <
        ((evaluate bits box inputs).lower : ℝ) := by
      exact_mod_cast hlower
    norm_num at hcast ⊢
    exact hcast
  exact hlowerReal.trans_le
    (evaluate_sound bits terms hpoint hvalid hinnerValid hcovers).1

end LRSmallSWideLogRoundedValue
end CourtadeKumar
