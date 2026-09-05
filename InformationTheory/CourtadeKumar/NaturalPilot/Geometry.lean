import InformationTheory.CourtadeKumar.NaturalPilot.B

/-! The same depth-eight geometry with a 20-step literal root enclosure and
a small rounded g0 receipt. No corner monotonicity or full evaluator imports. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalGeometry
open RationalEnclosure RootRatioBaseFaceD1Standalone RootRatioBaseFaceBStandalone

def yBounds : RationalEnclosure := mulNonnegative chiI eI
def byBounds : RationalEnclosure := add sI (mul (sub (point 1) sI) yBounds)
def vPayload : SqrtCertificate := ⟨(245005 / 262144), (245127 / 262144)⟩
def vBounds : RationalEnclosure := vPayload.enclosure
def logV : LogIntervalCertificate := { lower := ⟨-1, (245005 / 131072)⟩, upper := ⟨-1, (245127 / 131072)⟩ }
def logOnePlus : LogIntervalCertificate := { lower := ⟨0, (507149 / 262144)⟩, upper := ⟨0, (507271 / 262144)⟩ }
def logTwo : LogIntervalCertificate := { lower := ⟨1, 1⟩, upper := ⟨1, 1⟩ }
def g0I : RationalEnclosure :=
  sub (mul (add (point 1) (invPositive vBounds))
    (sub (logOnePlus.enclosure 8) (logTwo.enclosure 8))) (logV.enclosure 8)
def g0Bounds : RationalEnclosure := ⟨(-7047 / 4194304), (-11185 / 16777216)⟩

theorem v_checked : vPayload.check radicandI = true := by
  norm_num [vPayload, radicandI_eq, SqrtCertificate.check]
theorem v_positive : (0 : ℚ) < vBounds.lower := by
  norm_num [vBounds, vPayload, SqrtCertificate.enclosure]
theorem logV_checked : logV.check vBounds = true := by
  norm_num [logV, vBounds, vPayload, SqrtCertificate.enclosure,
    LogIntervalCertificate.check, LogRangeCertificate.check]
theorem logOnePlus_checked : logOnePlus.check (add (point 1) vBounds) = true := by
  norm_num [logOnePlus, vBounds, vPayload, SqrtCertificate.enclosure,
    LogIntervalCertificate.check, LogRangeCertificate.check, add, point]
theorem logTwo_checked : logTwo.check (point 2) = true := by
  norm_num [logTwo, LogIntervalCertificate.check, LogRangeCertificate.check, point]
theorem g0_cover : g0Bounds.lower ≤ g0I.lower ∧ g0I.upper ≤ g0Bounds.upper := by
  norm_num [g0Bounds, g0I, logV, logOnePlus, logTwo,
    vBounds, vPayload, SqrtCertificate.enclosure,
    LogIntervalCertificate.enclosure, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, invPositive, scale, mul, sub, add, neg,
    point, center, radius]

noncomputable def vValue (s k chi : ℝ) : ℝ :=
  Real.sqrt ((1 - s * k) / (1 - chi * (s * k)))
noncomputable def g0Value (v : ℝ) : ℝ :=
  (1 + v⁻¹) * (Real.log (1 + v) - Real.log 2) - Real.log v

theorem x_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    xI.Contains (1 - chi * (s * k)) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  exact contains_sub hOne (contains_mul hc (contains_mul hs hk))

theorem v_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    vBounds.Contains (vValue s k chi) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  exact SqrtCertificate.sound v_checked (contains_div (by norm_num [xI_eq])
    (contains_sub hOne (contains_mul hs hk)) (x_contains hs hk hc))

theorem y_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    yBounds.Contains (chi * (s * k)) := by
  apply contains_mulNonnegative (by norm_num [chiI]) ?_ hc (contains_mul hs hk)
  norm_num [eI, sI, kI, mul, point, center, radius]

theorem by_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    byBounds.Contains (s + (1 - s) * (chi * (s * k))) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  exact contains_add hs (contains_mul (contains_sub hOne hs) (y_contains hs hk hc))

theorem g0_contains {v : ℝ} (hv : vBounds.Contains v) :
    g0Bounds.Contains (g0Value v) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  have hTwo : (point 2).Contains (2 : ℝ) := by norm_num [point, Contains]
  have raw : g0I.Contains (g0Value v) :=
    contains_sub
      (contains_mul (contains_add hOne (contains_invPositive v_positive hv))
        (contains_sub (LogIntervalCertificate.sound 8 logOnePlus_checked (contains_add hOne hv))
          (LogIntervalCertificate.sound 8 logTwo_checked hTwo)))
      (LogIntervalCertificate.sound 8 logV_checked hv)
  have hlo : (g0Bounds.lower : ℝ) ≤ (g0I.lower : ℝ) := by exact_mod_cast g0_cover.1
  have hhi : (g0I.upper : ℝ) ≤ (g0Bounds.upper : ℝ) := by exact_mod_cast g0_cover.2
  exact ⟨hlo.trans raw.1, raw.2.trans hhi⟩

#print axioms CourtadeKumar.RootRatioNaturalGeometry.g0_contains
#print axioms CourtadeKumar.RootRatioNaturalGeometry.v_contains
end CourtadeKumar.RootRatioNaturalGeometry
