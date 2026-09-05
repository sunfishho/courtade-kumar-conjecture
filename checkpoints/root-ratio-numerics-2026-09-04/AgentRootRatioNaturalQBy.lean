import AgentRootRatioNaturalQSound

/-! A literal natural-interval Q/Q' receipt for the base-face pilot (by).
Both rounded enclosures include the whole input interval, not just a midpoint. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalQBy
open RationalEnclosure RootRatioNaturalQ

def input : RationalEnclosure := ⟨(17212943 / 134217728), (17259023 / 134217728)⟩
def payload : LRQPointCertificate where
  sqrtOneSub := ⟨(489419 / 524288), (122379 / 131072)⟩
  logLowerProbability := { lower := ⟨-5, (8693 / 8192)⟩, upper := ⟨-5, (34869 / 32768)⟩ }
  logUpperProbability := { lower := ⟨-1, (1013707 / 524288)⟩, upper := ⟨-1, (253451 / 131072)⟩ }
def qBounds : RationalEnclosure := ⟨(2440563 / 16777216), (2449007 / 16777216)⟩
def primeBounds : RationalEnclosure := ⟨(7568909 / 8388608), (15153767 / 16777216)⟩

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

#print axioms CourtadeKumar.RootRatioNaturalQBy.q_contains
#print axioms CourtadeKumar.RootRatioNaturalQBy.prime_contains
end CourtadeKumar.RootRatioNaturalQBy
