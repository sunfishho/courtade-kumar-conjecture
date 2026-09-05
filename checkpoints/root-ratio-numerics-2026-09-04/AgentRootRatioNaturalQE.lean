import AgentRootRatioNaturalQSound

/-! A literal natural-interval Q/Q' receipt for the base-face pilot (e).
Both rounded enclosures include the whole input interval, not just a midpoint. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalQE
open RationalEnclosure RootRatioNaturalQ

def input : RationalEnclosure := ⟨(767 / 4096), (769 / 4096)⟩
def payload : LRQPointCertificate where
  sqrtOneSub := ⟨(945031 / 1048576), (236329 / 262144)⟩
  logLowerProbability := { lower := ⟨-5, (25815 / 16384)⟩, upper := ⟨-5, (103545 / 65536)⟩ }
  logUpperProbability := { lower := ⟨-1, (1993607 / 1048576)⟩, upper := ⟨-1, (498473 / 262144)⟩ }
def qBounds : RationalEnclosure := ⟨(1645201 / 8388608), (412743 / 2097152)⟩
def primeBounds : RationalEnclosure := ⟨(6880279 / 8388608), (3444551 / 4194304)⟩

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

#print axioms CourtadeKumar.RootRatioNaturalQE.q_contains
#print axioms CourtadeKumar.RootRatioNaturalQE.prime_contains
end CourtadeKumar.RootRatioNaturalQE
