import InformationTheory.CourtadeKumar.LRSmallSWideLogSemanticCore
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRoundingCore
import InformationTheory.CourtadeKumar.LRDeterminantUpperKEnclosureCovers

/-!
# Scalar dyadically rounded evaluation for the small-s wide-log certificate

The final positivity check depends only on the value enclosure.  Computing
the three derivative enclosures would therefore be wasted work.  This module
projects the already-verified elementary interval-AD nodes to their value
components, then outward-rounds every scalar operation to a fixed dyadic
grid.  All concrete arithmetic remains small while the generic theorem below
retains the existing real semantics.
-/

namespace CourtadeKumar
namespace LRSmallSWideLogRounded

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLog
open LRUpperKDyadicOuterRounding

def rounded (bits : ℕ) (a : RationalEnclosure) : RationalEnclosure :=
  outerEnclosure bits a

def add (bits : ℕ) (a b : RationalEnclosure) : RationalEnclosure :=
  rounded bits (RationalEnclosure.add a b)

def sub (bits : ℕ) (a b : RationalEnclosure) : RationalEnclosure :=
  rounded bits (RationalEnclosure.sub a b)

def mul (bits : ℕ) (a b : RationalEnclosure) : RationalEnclosure :=
  rounded bits (RationalEnclosure.mul a b)

def divPositive (bits : ℕ)
    (a b : RationalEnclosure) : RationalEnclosure :=
  rounded bits (RationalEnclosure.div a b)

theorem rounded_contains (bits : ℕ) {a : RationalEnclosure} {x : ℝ}
    (ha : a.Contains x) : (rounded bits a).Contains x := by
  exact LRUpperKMidpointCoarsening.contains_of_covers
    (outerEnclosure_covers bits a) ha

theorem contains_add {bits : ℕ} {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (add bits a b).Contains (x + y) := by
  exact rounded_contains bits (RationalEnclosure.contains_add hx hy)

theorem contains_sub {bits : ℕ} {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (sub bits a b).Contains (x - y) := by
  exact rounded_contains bits (RationalEnclosure.contains_sub hx hy)

theorem contains_mul {bits : ℕ} {a b : RationalEnclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (mul bits a b).Contains (x * y) := by
  exact rounded_contains bits (RationalEnclosure.contains_mul hx hy)

theorem contains_divPositive {bits : ℕ}
    {a b : RationalEnclosure} {x y : ℝ}
    (hlower : (0 : ℚ) < b.lower)
    (hx : a.Contains x) (hy : b.Contains y) :
    (divPositive bits a b).Contains (x / y) := by
  exact rounded_contains bits (RationalEnclosure.contains_div hlower hx hy)

/-- Value-only evaluator.  The exact coordinate certificate is retained as
the input to `logOnePlusV`; every elementary output and every later operation
is rounded immediately. -/
def evaluate (bits terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate)
    (innerLog : WideLogData) : RationalEnclosure :=
  let s := (sAD box).value
  let k := (kAD box).value
  let chi := (chiAD box).value
  let vExact := certificate.coordinate.vAD box
  let logTwo := rounded bits
    (IntervalAD.log terms certificate.logTwo (IntervalAD.const 2)).value
  let logInner := rounded bits (wideLog innerLog (innerAD box)).value
  let logOuter := rounded bits
    (IntervalAD.log terms certificate.logOuter (outerAD box)).value
  let logK := rounded bits
    (IntervalAD.log terms certificate.logK (kAD box)).value
  let logOnePlusV := rounded bits
    (IntervalAD.log terms certificate.logOnePlusV
      (IntervalAD.add (IntervalAD.const 1) vExact)).value
  let logDArg := rounded bits
    (IntervalAD.log terms certificate.logDArg (dArgAD box)).value
  let qChi := rounded bits (qChiAD terms box certificate).value
  let A := divPositive bits
    (add bits (mul bits chi logInner) logOuter)
    (onePlusChiAD box).value
  let L := mul bits (RationalEnclosure.point 14) logTwo
  let p := sub bits
    (sub bits
      (add bits
        (add bits L (mul bits (RationalEnclosure.point 2) logTwo))
        (RationalEnclosure.point 1)) s) A
  let S := sub bits (sub bits (add bits logK qChi) s) A
  let b := sub bits logOnePlusV
    (divPositive bits logOuter (RationalEnclosure.point 2))
  let B := add bits (divPositive bits L (RationalEnclosure.point 2)) b
  let D := divPositive bits logDArg (RationalEnclosure.point 2)
  let scale := divPositive bits
    (mul bits k (add bits (RationalEnclosure.point 1) chi))
    (RationalEnclosure.point 4)
  let mainInner := add bits (mul bits D p) (mul bits B S)
  let main := mul bits scale mainInner
  let tail := divPositive bits (sub bits B D) (RationalEnclosure.point 4)
  add bits main tail

theorem evaluate_sound
    (bits terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate} {innerLog : WideLogData}
    (hpoint : box.Contains point)
    (hvalid : WideCertificateValid box certificate)
    (hinnerValid : innerLog.Valid terms (innerAD box)) :
    (evaluate bits terms box certificate innerLog).Contains
      (lrSmallSBridgeCoreTarget point) := by
  have hs : (sAD box).value.Contains point.s :=
    (IntervalAD.contains_variableS
      (show box.sInterval.Contains point.s from
        ⟨hpoint.1, hpoint.2.1⟩)).1
  have hk : (kAD box).value.Contains point.k :=
    (IntervalAD.contains_variableK
      (show box.kInterval.Contains point.k from
        ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)).1
  have hchi : (chiAD box).value.Contains point.chi :=
    (IntervalAD.contains_variableChi
      (show box.chiInterval.Contains point.chi from
        ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)).1
  have hr := IntervalAD.contains_sub (IntervalAD.contains_const 1)
    (IntervalAD.contains_variableS
      (show box.sInterval.Contains point.s from
        ⟨hpoint.1, hpoint.2.1⟩))
  have hkAD := IntervalAD.contains_variableK
    (show box.kInterval.Contains point.k from
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  have hchiAD := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains point.chi from
      ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩)
  have houter := IntervalAD.contains_add (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul hr hkAD)
  have hinner := IntervalAD.contains_add (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul (IntervalAD.contains_mul hr hkAD) hchiAD)
  have honeChi := IntervalAD.contains_add (IntervalAD.contains_const 1) hchiAD
  have hv := certificate.coordinate.vAD_sound hpoint hvalid.coordinate
  have honeV := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have hdArg := IntervalAD.contains_divPositive hvalid.kPositive houter hkAD
  have hlogTwo := rounded_contains bits
    (IntervalAD.contains_log terms hvalid.logTwo
      (IntervalAD.contains_const 2)).1
  have hlogInner := rounded_contains bits
    (contains_wideLog terms hinnerValid hinner).1
  have hlogOuter := rounded_contains bits
    (IntervalAD.contains_log terms hvalid.logOuter houter).1
  have hlogK := rounded_contains bits
    (IntervalAD.contains_log terms hvalid.logK hkAD).1
  have hlogOnePlusV := rounded_contains bits
    (IntervalAD.contains_log terms hvalid.logOnePlusV honeV).1
  have hlogDArg := rounded_contains bits
    (IntervalAD.contains_log terms hvalid.logDArg hdArg).1
  rcases qChiAD_sound_of_logChi terms hpoint hvalid.logChi
      hvalid.onePlusChiPositive with ⟨qS, qK, qC, hqExact⟩
  have hq := rounded_contains bits hqExact.1
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

theorem positive_of_evaluate
    (bits terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRSmallSBridgeCoreCertificate} {innerLog : WideLogData}
    (hpoint : box.Contains point)
    (hvalid : WideCertificateValid box certificate)
    (hinnerValid : innerLog.Valid terms (innerAD box))
    (hlower : (2 / 3 : ℚ) <
      (evaluate bits terms box certificate innerLog).lower) :
    (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point := by
  have hlowerReal : (2 / 3 : ℝ) <
      ((evaluate bits terms box certificate innerLog).lower : ℝ) := by
    have hcast : (((2 / 3 : ℚ) : ℚ) : ℝ) <
        ((evaluate bits terms box certificate innerLog).lower : ℝ) := by
      exact_mod_cast hlower
    norm_num at hcast ⊢
    exact hcast
  exact hlowerReal.trans_le
    (evaluate_sound bits terms hpoint hvalid hinnerValid).1

end LRSmallSWideLogRounded
end CourtadeKumar
