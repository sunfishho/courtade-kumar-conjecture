import InformationTheory.CourtadeKumar.AnalyticExtension.CompactCheckerCore
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactADSound
import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointRationalExprSound
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Every logarithm and tangent coefficient supplied by a compact leaf is checked here. -/
open Set
namespace CourtadeKumar.LRCompactReducedCertificate

lemma EndpointLog.positive {d : EndpointLog} {x : ℚ} (h : d.check x = true) : 0 < x := by
  simpa only [EndpointLog.check, Bool.and_eq_true, decide_eq_true_eq] using
    (Bool.and_eq_true_iff.mp h).1

lemma EndpointLog.sound {d : EndpointLog} {x : ℚ} (h : d.check x = true) :
    d.enclosure.Contains (Real.log (x : ℝ)) := by
  have hw := (Bool.and_eq_true_iff.mp h).2
  have hs := LRMidpointReducedCertificate.RoundedLog.sound hw
  cases hd : d.reciprocal with
  | false => simpa [EndpointLog.enclosure, hd] using hs
  | true =>
    simp only [hd, Bool.true_eq, if_true, Rat.cast_inv, Real.log_inv] at hs
    constructor <;> simp only [EndpointLog.enclosure, hd, Bool.true_eq, if_true, Rat.cast_neg] <;>
      linarith [hs.1,hs.2]

lemma LogInterval.positive {d : LogInterval} {a : RationalEnclosure} (h : d.check a = true) :
    0 < a.lower := EndpointLog.positive (Bool.and_eq_true_iff.mp h).1

lemma LogInterval.sound {d : LogInterval} {a : RationalEnclosure} {x : ℝ}
    (h : d.check a = true) (hx : a.Contains x) : d.enclosure.Contains (Real.log x) := by
  have hp := LogInterval.positive h
  have hr : (0 : ℝ) < a.lower := by exact_mod_cast hp
  have hs := (Bool.and_eq_true_iff.mp h)
  have hlo := EndpointLog.sound hs.1
  have hhi := EndpointLog.sound hs.2
  exact ⟨hlo.1.trans (Real.log_le_log hr hx.1),
    (Real.log_le_log (hr.trans_le hx.1) hx.2).trans hhi.2⟩

lemma constInterval_models {a : RationalEnclosure} {x z r v t : ℝ} (hx : a.Contains x) :
    (constInterval a).Models (fun _ => x) z r v t := by
  refine ⟨0,0,0,⟨hx,?_,?_,?_⟩,?_⟩
  · simpa using RationalEnclosure.contains_point 0
  · simpa using RationalEnclosure.contains_point 0
  · simpa using RationalEnclosure.contains_point 0
  · simpa using hasDerivAt_const z x

noncomputable def bValue (R v t : ℝ) : ℝ :=
  Real.log (1+v) - Real.log (1-R*(v^2*t^2))/2

lemma BData.models {d : BData} {R v t : Jet} {fR fv ft : ℝ → ℝ} {z wr wv wt : ℝ}
    (hR : R.Models fR z wr wv wt) (hv : v.Models fv z wr wv wt)
    (ht : t.Models ft z wr wv wt) (hpv : 0 ≤ v.bounds.value.lower)
    (hpt : 0 ≤ t.bounds.value.lower) (hcheck : d.check R v t = true) :
    (d.jet R v t).Models (fun x => bValue (fR x) (fv x) (ft x)) z wr wv wt := by
  have hc : ((bLogInputs R v t).1.valid = true ∧ (bLogInputs R v t).2.valid = true) ∧
      d.logV.check (bLogInputs R v t).1.bounds.value = true ∧
      d.logS.check (bLogInputs R v t).2.bounds.value = true := by
    simpa only [BData.check, Bool.and_eq_true, and_assoc] using hcheck
  have h1 := Jet.models_add (Jet.models_const 1) hv
  have h2 := Jet.models_sub (Jet.models_const 1)
    (Jet.models_mul hR (Jet.models_mul (Jet.models_pow hv hpv 2) (Jet.models_pow ht hpt 2)))
  simp only [Rat.cast_one] at h1 h2
  have hv1 : (bLogInputs R v t).1.bounds.value.Contains (1+fv z) := by
    rcases h1 with ⟨ds,dk,dc,h,_⟩
    simpa only [Rat.cast_one] using h.1
  have hv2 : (bLogInputs R v t).2.bounds.value.Contains (1-fR z*(fv z^2*ft z^2)) := by
    rcases h2 with ⟨ds,dk,dc,h,_⟩
    simpa only [Rat.cast_one] using h.1
  have hl1 := Jet.models_logWith h1 (LogInterval.positive hc.2.1)
    (LogInterval.sound hc.2.1 hv1)
  have hl2 := Jet.models_logWith h2 (LogInterval.positive hc.2.2)
    (LogInterval.sound hc.2.2 hv2)
  simpa only [bValue, Rat.cast_one, Rat.cast_ofNat] using
    Jet.models_sub hl1 (Jet.models_div hl2 (Jet.models_const 2)
      (by norm_num [Jet.const, IntervalAD.const, RationalEnclosure.point]))

theorem TangentData.sound {d : TangentData} {a b : ℚ} (h : d.check a b = true) :
    (a : ℝ) ∈ Ioo (-1 : ℝ) 1 ∧ (b : ℝ) ∈ Ioo (-1 : ℝ) 1 ∧
    (d.aT : ℝ) ≤ Real.artanh (a : ℝ) + Real.artanh (b : ℝ) ∧
    (d.au : ℝ) ≤ Real.log (1-(b : ℝ)^2)/2 ∧
    (d.ac : ℝ) ≤ Real.log (1-(a : ℝ)^2)/2 := by
  have hc : (((0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ b < 1) ∧
      d.logA.check ((1+a)/(1-a)) = true) ∧ d.logB.check ((1+b)/(1-b)) = true) ∧
      d.logU.check (1/(1-b^2)) = true ∧ d.logC.check (1/(1-a^2)) = true := by
    simpa only [TangentData.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
  have ha0 : (0:ℝ) ≤ a := by exact_mod_cast hc.1.1.1.1
  have hb0 : (0:ℝ) ≤ b := by exact_mod_cast hc.1.1.1.2.2.1
  have ha1 : (a:ℝ) < 1 := by exact_mod_cast hc.1.1.1.2.1
  have hb1 : (b:ℝ) < 1 := by exact_mod_cast hc.1.1.1.2.2.2
  have ha : (a:ℝ) ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,ha1⟩
  have hb : (b:ℝ) ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hb1⟩
  have hA := LRMidpointReducedCertificate.RoundedLog.sound hc.1.1.2
  have hB := LRMidpointReducedCertificate.RoundedLog.sound hc.1.2
  have hU := LRMidpointReducedCertificate.RoundedLog.sound hc.2.1
  have hC := LRMidpointReducedCertificate.RoundedLog.sound hc.2.2
  push_cast at hA hB hU hC
  rw [one_div,Real.log_inv] at hU hC
  refine ⟨ha,hb,?_,?_,?_⟩
  · rw [Real.artanh_eq_half_log ⟨ha.1.le,ha.2.le⟩,
      Real.artanh_eq_half_log ⟨hb.1.le,hb.2.le⟩]
    simp only [TangentData.aT, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    linarith [hA.1,hB.1]
  · simp only [TangentData.au, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
    linarith [hU.2]
  · simp only [TangentData.ac, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
    linarith [hC.2]

end CourtadeKumar.LRCompactReducedCertificate
