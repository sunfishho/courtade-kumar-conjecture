import AgentRootRatioBaseFaceD1Standalone
import InformationTheory.CourtadeKumar.ExactSqrtEnclosure

/-! Small exact B enclosure for the same base-face pilot. The square-root
and logarithm data are literal proposals, checked by ordinary norm_num.
No full D9 or automatic certificate-generation environment is imported. -/

set_option autoImplicit false

namespace CourtadeKumar.RootRatioBaseFaceBStandalone

open RationalEnclosure RootRatioBaseFaceRoundedPilot RootRatioBaseFaceD1Standalone

def chiI : RationalEnclosure := ⟨767 / 2048, 769 / 2048⟩
def xI : RationalEnclosure := sub (point 1) (mul chiI eI)
def radicandI : RationalEnclosure := div (sub (point 1) eI) xI
def vCertificate : SqrtCertificate := ⟨957 / 1024, 3831 / 4096⟩
def vI : RationalEnclosure := vCertificate.enclosure
def beI : RationalEnclosure := add sI (mul (sub (point 1) sI) eI)

def logOnePlusCertificate : LogIntervalCertificate where
  lower := ⟨0, 1981 / 1024⟩
  upper := ⟨0, 7927 / 4096⟩

def logBeCertificate : LogIntervalCertificate where
  lower := ⟨-3, 15601 / 8192⟩
  upper := ⟨-3, 15631 / 8192⟩

def bI : RationalEnclosure :=
  sub (logOnePlusCertificate.enclosure 8)
    (mul (point (1 / 2)) (logBeCertificate.enclosure 8))

theorem xI_eq : xI = ⟨7797247 / 8388608, 7800321 / 8388608⟩ := by
  norm_num [xI, chiI, eI, sI, kI, mul, sub, add, neg, point, center, radius]

theorem radicandI_eq :
    radicandI = ⟨53128064399360 / 60821029516287, 6817792 / 7797247⟩ := by
  norm_num [radicandI, xI_eq, eI, sI, kI, div, invPositive,
    mul, sub, add, neg, point, center, radius]

theorem beI_eq : beI = ⟨15601 / 65536, 15631 / 65536⟩ := by
  norm_num [beI, eI, sI, kI, mul, sub, add, neg, point, center, radius]

theorem sqrt_checked : vCertificate.check radicandI = true := by
  norm_num [vCertificate, radicandI_eq, SqrtCertificate.check]

theorem logOnePlus_checked :
    logOnePlusCertificate.check (add (point 1) vI) = true := by
  norm_num [logOnePlusCertificate, vI, vCertificate, SqrtCertificate.enclosure,
    LogIntervalCertificate.check, LogRangeCertificate.check, add, point]

theorem logBe_checked : logBeCertificate.check beI = true := by
  norm_num [logBeCertificate, beI_eq, LogIntervalCertificate.check,
    LogRangeCertificate.check]

theorem rounded_cover :
    pilot8Bounds.b.lower ≤ bI.lower ∧ bI.upper ≤ pilot8Bounds.b.upper := by
  norm_num [bI, pilot8Bounds, logOnePlusCertificate, logBeCertificate,
    LogIntervalCertificate.enclosure, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, scale, mul, sub, add, neg, point, center, radius]

noncomputable def bValue (s k chi : ℝ) : ℝ :=
  Real.log (1 + Real.sqrt ((1 - s * k) / (1 - chi * (s * k)))) -
    (1 / 2) * Real.log (s + (1 - s) * (s * k))

theorem bI_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    bI.Contains (bValue s k chi) := by
  have hOne : (point 1).Contains (1 : ℝ) := by norm_num [point, Contains]
  have hHalf : (point (1 / 2)).Contains (1 / 2 : ℝ) := by
    norm_num [point, Contains]
  have he : eI.Contains (s * k) := contains_mul hs hk
  have hx : xI.Contains (1 - chi * (s * k)) :=
    contains_sub hOne (contains_mul hc he)
  have hr : radicandI.Contains ((1 - s * k) / (1 - chi * (s * k))) :=
    contains_div (by norm_num [xI_eq]) (contains_sub hOne he) hx
  have hv := SqrtCertificate.sound sqrt_checked hr
  have hb : beI.Contains (s + (1 - s) * (s * k)) :=
    contains_add hs (contains_mul (contains_sub hOne hs) he)
  have hlv := LogIntervalCertificate.sound 8 logOnePlus_checked
    (contains_add hOne hv)
  have hlb := LogIntervalCertificate.sound 8 logBe_checked hb
  exact contains_sub hlv (contains_mul hHalf hlb)

theorem rounded_contains {s k chi : ℝ}
    (hs : sI.Contains s) (hk : kI.Contains k) (hc : chiI.Contains chi) :
    pilot8Bounds.b.Contains (bValue s k chi) := by
  have h := bI_contains hs hk hc
  have hlo : (pilot8Bounds.b.lower : ℝ) ≤ (bI.lower : ℝ) := by
    exact_mod_cast rounded_cover.1
  have hhi : (bI.upper : ℝ) ≤ (pilot8Bounds.b.upper : ℝ) := by
    exact_mod_cast rounded_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

#print axioms CourtadeKumar.RootRatioBaseFaceBStandalone.rounded_cover
#print axioms CourtadeKumar.RootRatioBaseFaceBStandalone.rounded_contains

end CourtadeKumar.RootRatioBaseFaceBStandalone
