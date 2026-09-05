import InformationTheory.CourtadeKumar.ExactLogEnclosure
import InformationTheory.CourtadeKumar.NaturalPilot.Bounds

/-!
# A small standalone D1 enclosure for the actual base-face pilot

No full D9 evaluator, automatic payload generator, or root-ratio calculus is
imported. The interval expressions follow the production D1 value formula;
their rational checks and real soundness are proved here independently.
The final production-name bridge is kept in a separate module.
-/

set_option autoImplicit false

namespace CourtadeKumar.RootRatioBaseFaceD1Standalone

open RationalEnclosure RootRatioBaseFaceRoundedPilot

def sI : RationalEnclosure := point (1 / 16)
def kI : RationalEnclosure := ⟨767 / 256, 769 / 256⟩
def eI : RationalEnclosure := mul sI kI
def yI : RationalEnclosure := div (sub (add (point 1) kI) eI) kI
def meanI : RationalEnclosure := mul (add (point 1) yI) (point (1 / 2))
def denominatorI : RationalEnclosure := add (mul (point 3) yI) (point 1)

def logMeanCertificate : LogIntervalCertificate where
  lower := ⟨0, 21401567 / 18874336⟩
  upper := ⟨0, 27905 / 24544⟩

def d1I : RationalEnclosure :=
  add (mul (point (1 / 2)) (logMeanCertificate.enclosure 8))
    (div (sub yI (point 1)) denominatorI)

theorem yI_eq : yI = ⟨11964399 / 9437168, 15633 / 12272⟩ := by
  norm_num [yI, eI, sI, kI, div, invPositive, mul, sub, add, neg,
    point, center, radius]

theorem meanI_eq : meanI = ⟨21401567 / 18874336, 27905 / 24544⟩ := by
  norm_num [meanI, yI_eq, mul, add, point, center, radius]

theorem denominatorI_eq : denominatorI = ⟨45330365 / 9437168, 59171 / 12272⟩ := by
  norm_num [denominatorI, yI_eq, mul, add, point, center, radius]

theorem logMean_checked : logMeanCertificate.check meanI = true := by
  norm_num [logMeanCertificate, meanI_eq, LogIntervalCertificate.check,
    LogRangeCertificate.check]

theorem denominator_positive : (0 : ℚ) < denominatorI.lower := by
  norm_num [denominatorI_eq]

theorem rounded_cover :
    pilot8Bounds.d1.lower ≤ d1I.lower ∧ d1I.upper ≤ pilot8Bounds.d1.upper := by
  norm_num [d1I, pilot8Bounds, yI_eq, denominatorI_eq,
    logMeanCertificate, LogIntervalCertificate.enclosure,
    LogRangeCertificate.enclosure, logScaledMantissaEnclosure,
    logTwoEnclosure, logMantissaEnclosure, halfLogRatioEnclosure,
    logRatioCoordinate, atanhPartial, atanhTail, Finset.sum_range_succ,
    div, invPositive, scale, mul, sub, add, neg, point, center, radius]

noncomputable def d1Value (s k : ℝ) : ℝ :=
  let y := (1 + k - s * k) / k
  (1 / 2) * Real.log ((1 + y) / 2) + (y - 1) / (3 * y + 1)

theorem d1I_contains {s k : ℝ} (hs : sI.Contains s) (hk : kI.Contains k) :
    d1I.Contains (d1Value s k) := by
  have hOne : (point 1).Contains (1 : ℝ) := by
    norm_num [point, Contains]
  have hThree : (point 3).Contains (3 : ℝ) := by
    norm_num [point, Contains]
  have hHalf : (point (1 / 2)).Contains (1 / 2 : ℝ) := by
    norm_num [point, Contains]
  have he : eI.Contains (s * k) := contains_mul hs hk
  have hy : yI.Contains ((1 + k - s * k) / k) := by
    apply contains_div (by norm_num [kI]) _ hk
    exact contains_sub (contains_add hOne hk) he
  have hm : meanI.Contains ((1 + (1 + k - s * k) / k) / 2) := by
    simpa only [meanI, div_eq_mul_inv, one_mul] using
      contains_mul (contains_add hOne hy) hHalf
  have hd : denominatorI.Contains (3 * ((1 + k - s * k) / k) + 1) :=
    contains_add (contains_mul hThree hy) hOne
  have hl := LogIntervalCertificate.sound 8 logMean_checked hm
  have hf := contains_div denominator_positive
    (contains_sub hy hOne) hd
  exact contains_add (contains_mul hHalf hl) hf

theorem rounded_contains {s k : ℝ} (hs : sI.Contains s) (hk : kI.Contains k) :
    pilot8Bounds.d1.Contains (d1Value s k) := by
  have h := d1I_contains hs hk
  have hlo : (pilot8Bounds.d1.lower : ℝ) ≤ (d1I.lower : ℝ) := by
    exact_mod_cast rounded_cover.1
  have hhi : (d1I.upper : ℝ) ≤ (pilot8Bounds.d1.upper : ℝ) := by
    exact_mod_cast rounded_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

#print axioms CourtadeKumar.RootRatioBaseFaceD1Standalone.rounded_cover
#print axioms CourtadeKumar.RootRatioBaseFaceD1Standalone.rounded_contains

end CourtadeKumar.RootRatioBaseFaceD1Standalone
