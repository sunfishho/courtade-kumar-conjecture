import InformationTheory.CourtadeKumar.NaturalPilot.QInterval

/-! A literal natural-interval Q/Q' receipt for the base-face pilot (be).
Both rounded enclosures include the whole input interval, not just a midpoint. -/
set_option autoImplicit false
namespace CourtadeKumar.RootRatioNaturalQBe
open RationalEnclosure RootRatioNaturalQ

def input : RationalEnclosure := ⟨(15601 / 65536), (15631 / 65536)⟩
def payload : LRQPointCertificate where
  sqrtOneSub := ⟨(457511 / 524288), (457649 / 524288)⟩
  logLowerProbability := { lower := ⟨-4, (66639 / 65536)⟩, upper := ⟨-4, (66777 / 65536)⟩ }
  logUpperProbability := { lower := ⟨-1, (981799 / 524288)⟩, upper := ⟨-1, (981937 / 524288)⟩ }
def qBounds : RationalEnclosure := ⟨(1983827 / 8388608), (3978301 / 16777216)⟩
def primeBounds : RationalEnclosure := ⟨(1614511 / 2097152), (6465303 / 8388608)⟩

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

#print axioms CourtadeKumar.RootRatioNaturalQBe.q_contains
#print axioms CourtadeKumar.RootRatioNaturalQBe.prime_contains
end CourtadeKumar.RootRatioNaturalQBe
