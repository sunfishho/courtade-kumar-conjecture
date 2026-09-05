import AgentRootRatioNaturalQSound

/-! A literal natural-interval Q/Q' receipt for the base-face pilot (y).
Both rounded enclosures include the whole input interval, not just a midpoint. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalQY
open RationalEnclosure RootRatioNaturalQ

def input : RationalEnclosure := ⟨(588289 / 8388608), (591361 / 8388608)⟩
def payload : LRQPointCertificate where
  sqrtOneSub := ⟨(252735 / 262144), (252785 / 262144)⟩
  logLowerProbability := { lower := ⟨-6, (9359 / 8192)⟩, upper := ⟨-6, (9409 / 8192)⟩ }
  logUpperProbability := { lower := ⟨-1, (514879 / 262144)⟩, upper := ⟨-1, (514929 / 262144)⟩ }
def qBounds : RationalEnclosure := ⟨(1500819 / 16777216), (1510491 / 16777216)⟩
def primeBounds : RationalEnclosure := ⟨(8704109 / 8388608), (17435269 / 16777216)⟩

theorem checked : naturalCheck input payload = true := by
  norm_num [naturalCheck, input, payload, LRQPointCertificate.lowerProbability,
    LRQPointCertificate.upperProbability, LRQPointCertificate.sqrtEnclosure,
    SqrtCertificate.check, SqrtCertificate.enclosure,
    LogIntervalCertificate.check, LogRangeCertificate.check,
    scale, mul, sub, add, neg, point, center, radius]

theorem root_positive : (0 : ℚ) < payload.sqrtEnclosure.lower := by
  norm_num [payload, LRQPointCertificate.sqrtEnclosure, SqrtCertificate.enclosure]

theorem q_cover : qBounds.lower ≤ (payload.enclosure 8).lower ∧
    (payload.enclosure 8).upper ≤ qBounds.upper := by
  norm_num [qBounds, payload, LRQPointCertificate.enclosure, LRQPointCertificate.primeEnclosure,
    LRQPointCertificate.lowerProbability, LRQPointCertificate.upperProbability,
    LRQPointCertificate.sqrtEnclosure, SqrtCertificate.enclosure,
    LogIntervalCertificate.enclosure, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, div, invPositive, scale, mul, sub, add, neg, point, center, radius]

theorem prime_cover : primeBounds.lower ≤ (payload.primeEnclosure 8).lower ∧
    (payload.primeEnclosure 8).upper ≤ primeBounds.upper := by
  norm_num [primeBounds, payload, LRQPointCertificate.enclosure, LRQPointCertificate.primeEnclosure,
    LRQPointCertificate.lowerProbability, LRQPointCertificate.upperProbability,
    LRQPointCertificate.sqrtEnclosure, SqrtCertificate.enclosure,
    LogIntervalCertificate.enclosure, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, div, invPositive, scale, mul, sub, add, neg, point, center, radius]

theorem q_contains {x : ℝ} (hx : input.Contains x) :
    qBounds.Contains (lrCertificateQ x) := by
  have h := RootRatioNaturalQ.sound 8 checked hx
  have hlo : (qBounds.lower : ℝ) ≤ ((payload.enclosure 8).lower : ℝ) := by
    exact_mod_cast q_cover.1
  have hhi : ((payload.enclosure 8).upper : ℝ) ≤ (qBounds.upper : ℝ) := by
    exact_mod_cast q_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

theorem prime_contains {x : ℝ} (hx : input.Contains x) :
    primeBounds.Contains (lrCertificateQPrime x) := by
  have hdomain : x ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num [input, Contains] at hx
    constructor <;> linarith [hx.1, hx.2]
  have h := RootRatioNaturalQ.prime_sound 8 hdomain checked root_positive hx
  have hlo : (primeBounds.lower : ℝ) ≤ ((payload.primeEnclosure 8).lower : ℝ) := by
    exact_mod_cast prime_cover.1
  have hhi : ((payload.primeEnclosure 8).upper : ℝ) ≤ (primeBounds.upper : ℝ) := by
    exact_mod_cast prime_cover.2
  exact ⟨hlo.trans h.1, h.2.trans hhi⟩

#print axioms CourtadeKumar.RootRatioNaturalQY.q_contains
#print axioms CourtadeKumar.RootRatioNaturalQY.prime_contains
end CourtadeKumar.RootRatioNaturalQY
