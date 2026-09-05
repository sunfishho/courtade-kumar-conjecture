import InformationTheory.CourtadeKumar.NaturalPilot.D1Coarse

/-! Sharpen D1 by eliminating repeated k before interval evaluation:
Y = (1+k-sk)/k = 1 + 1/k - s. Same physical box, no subdivision. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioBaseFaceD1Sharp
open RationalEnclosure RootRatioBaseFaceD1Standalone

def sharpYI : RationalEnclosure := sub (add (point 1) (invPositive kI)) sI
def meanI : RationalEnclosure := scale (1 / 2) (add (point 1) sharpYI)
def denI : RationalEnclosure := add (scale 3 sharpYI) (point 1)
def logMean : LogIntervalCertificate where
  lower := ⟨0, 27935 / 24608⟩
  upper := ⟨0, 27873 / 24544⟩
def valueI : RationalEnclosure := add (scale (1 / 2) (logMean.enclosure 8))
  (div (sub sharpYI (point 1)) denI)
def bounds : RationalEnclosure := ⟨1003077 / 8388608, 2012899 / 16777216⟩

theorem sharpYI_eq : sharpYI = ⟨15631 / 12304, 15601 / 12272⟩ := by
  norm_num [sharpYI, kI, sI, invPositive, sub, add, neg, point]
theorem log_checked : logMean.check meanI = true := by
  norm_num [logMean, meanI, sharpYI_eq, LogIntervalCertificate.check,
    LogRangeCertificate.check, scale, mul, add, point, center, radius]
theorem den_positive : (0 : ℚ) < denI.lower := by
  norm_num [denI, sharpYI_eq, scale, mul, add, point, center, radius]
theorem rounded_cover : bounds.lower ≤ valueI.lower ∧ valueI.upper ≤ bounds.upper := by
  norm_num [bounds, valueI, denI, sharpYI_eq, logMean,
    LogIntervalCertificate.enclosure, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, div, invPositive, scale, mul, sub, add, neg,
    point, center, radius]

theorem value_contains {s k : ℝ} (hs : sI.Contains s) (hk : kI.Contains k) :
    valueI.Contains (d1Value s k) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  have hThree : (point 3).Contains (3 : ℝ) := by norm_num [point, Contains]
  have hHalf : (point (1 / 2)).Contains (1 / 2 : ℝ) := by norm_num [point, Contains]
  have hkpos : 0 < k := by
    have h := hk.1
    norm_num [kI] at h
    linarith
  have hy0 : sharpYI.Contains (1 + k⁻¹ - s) :=
    contains_sub (contains_add hOne (contains_invPositive (by norm_num [kI]) hk)) hs
  have heq : 1 + k⁻¹ - s = (1 + k - s * k) / k := by
    field_simp [hkpos.ne']
    <;> ring
  rw [heq] at hy0
  have hm : meanI.Contains ((1 + (1 + k - s * k) / k) / 2) := by
    have h := contains_mul hHalf (contains_add hOne hy0)
    simpa only [meanI, scale, div_eq_mul_inv, one_mul, mul_comm] using h
  have hd : denI.Contains (3 * ((1 + k - s * k) / k) + 1) :=
    contains_add (contains_mul hThree hy0) hOne
  exact contains_add (contains_mul hHalf (LogIntervalCertificate.sound 8 log_checked hm))
    (contains_div den_positive (contains_sub hy0 hOne) hd)

theorem rounded_contains {s k : ℝ} (hs : sI.Contains s) (hk : kI.Contains k) :
    bounds.Contains (d1Value s k) := by
  have h := value_contains hs hk
  have hlo : (bounds.lower : ℝ) ≤ (valueI.lower : ℝ) := by exact_mod_cast rounded_cover.1
  have hhi : (valueI.upper : ℝ) ≤ (bounds.upper : ℝ) := by exact_mod_cast rounded_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

#print axioms CourtadeKumar.RootRatioBaseFaceD1Sharp.rounded_contains
end CourtadeKumar.RootRatioBaseFaceD1Sharp
