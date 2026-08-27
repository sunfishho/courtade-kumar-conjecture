import InformationTheory.CourtadeKumar.LRCertificateQ
import InformationTheory.CourtadeKumar.ExactLogEnclosure
import InformationTheory.CourtadeKumar.ExactSqrtEnclosure

/-!
# Executable endpoint enclosures for the LR entropy scalar

The external generator supplies only range-reduction and square-root data.
Lean checks those data, reconstructs the binary-entropy expression using exact
rational interval arithmetic, and proves that the resulting interval contains
the actual `lrCertificateQ` value.
-/

open Set

namespace CourtadeKumar

/-- Untrusted auxiliary data for evaluating `Q` at one rational point. -/
structure LRQPointCertificate where
  sqrtOneSub : RationalEnclosure.SqrtCertificate
  logLowerProbability : RationalEnclosure.LogIntervalCertificate
  logUpperProbability : RationalEnclosure.LogIntervalCertificate

namespace LRQPointCertificate

def sqrtInput (y : ℚ) : RationalEnclosure :=
  RationalEnclosure.point (1 - y)

def sqrtEnclosure (certificate : LRQPointCertificate) : RationalEnclosure :=
  certificate.sqrtOneSub.enclosure

def lowerProbability (certificate : LRQPointCertificate) : RationalEnclosure :=
  RationalEnclosure.scale (1 / 2)
    (RationalEnclosure.sub (RationalEnclosure.point 1)
      certificate.sqrtEnclosure)

def upperProbability (certificate : LRQPointCertificate) : RationalEnclosure :=
  RationalEnclosure.scale (1 / 2)
    (RationalEnclosure.add (RationalEnclosure.point 1)
      certificate.sqrtEnclosure)

/-- Executable checker for all non-algebraic data in a point evaluation. -/
def check (y : ℚ) (certificate : LRQPointCertificate) : Bool :=
  certificate.sqrtOneSub.check (sqrtInput y) &&
    certificate.logLowerProbability.check certificate.lowerProbability &&
    certificate.logUpperProbability.check certificate.upperProbability

/-- The exact interval expression `-p log p -(1-p) log(1-p)`. -/
def enclosure (terms : ℕ) (certificate : LRQPointCertificate) :
    RationalEnclosure :=
  RationalEnclosure.neg (RationalEnclosure.add
    (RationalEnclosure.mul certificate.lowerProbability
      (certificate.logLowerProbability.enclosure terms))
    (RationalEnclosure.mul certificate.upperProbability
      (certificate.logUpperProbability.enclosure terms)))

theorem sound (terms : ℕ) {y : ℚ} {certificate : LRQPointCertificate}
    (hcheck : certificate.check y = true) :
    (certificate.enclosure terms).Contains (lrCertificateQ (y : ℝ)) := by
  have hparts :
      certificate.sqrtOneSub.check (sqrtInput y) = true ∧
      certificate.logLowerProbability.check certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check (sqrtInput y) = true ∧
          certificate.logLowerProbability.check certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check certificate.upperProbability = true := by
      simpa [check] using hcheck
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput : (sqrtInput y).Contains (1 - (y : ℝ)) := by
    simpa [sqrtInput] using RationalEnclosure.contains_point (1 - y)
  have hsqrt := certificate.sqrtOneSub.sound hparts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [lowerProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hadd := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hadd
    simpa [upperProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hlogLower := certificate.logLowerProbability.sound terms
    hparts.2.1 hlower
  have hlogUpper := certificate.logUpperProbability.sound terms
    hparts.2.2 hupper
  have hfirst := RationalEnclosure.contains_mul hlower hlogLower
  have hsecond := RationalEnclosure.contains_mul hupper hlogUpper
  have hsum := RationalEnclosure.contains_add hfirst hsecond
  have hneg := RationalEnclosure.contains_neg hsum
  have hidentity :
      -(((1 - Real.sqrt (1 - (y : ℝ))) / 2) *
          Real.log ((1 - Real.sqrt (1 - (y : ℝ))) / 2) +
        ((1 + Real.sqrt (1 - (y : ℝ))) / 2) *
          Real.log ((1 + Real.sqrt (1 - (y : ℝ))) / 2)) =
        lrCertificateQ (y : ℝ) := by
    unfold lrCertificateQ
    rw [topJ_eq_binEntropy, Real.binEntropy, Real.log_inv, Real.log_inv]
    ring_nf
  simpa [enclosure, hidentity] using hneg

/-- The derivative evaluator additionally checks that the square-root
interval stays strictly away from zero, as required by interval division. -/
def primeCheck (y : ℚ) (certificate : LRQPointCertificate) : Bool :=
  certificate.check y && decide ((0 : ℚ) < certificate.sqrtEnclosure.lower)

def primeEnclosure (terms : ℕ) (certificate : LRQPointCertificate) :
    RationalEnclosure :=
  RationalEnclosure.scale (1 / 4)
    (RationalEnclosure.div
      (RationalEnclosure.sub
        (certificate.logUpperProbability.enclosure terms)
        (certificate.logLowerProbability.enclosure terms))
      certificate.sqrtEnclosure)

theorem prime_sound (terms : ℕ) {y : ℚ}
    (hy : y ∈ Ioo (0 : ℚ) 1) {certificate : LRQPointCertificate}
    (hcheck : certificate.primeCheck y = true) :
    (certificate.primeEnclosure terms).Contains
      (lrCertificateQPrime (y : ℝ)) := by
  have hprimeParts : certificate.check y = true ∧
      (0 : ℚ) < certificate.sqrtEnclosure.lower := by
    simpa [primeCheck] using hcheck
  have hparts :
      certificate.sqrtOneSub.check (sqrtInput y) = true ∧
      certificate.logLowerProbability.check certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check (sqrtInput y) = true ∧
          certificate.logLowerProbability.check certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check certificate.upperProbability = true := by
      simpa [check] using hprimeParts.1
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput : (sqrtInput y).Contains (1 - (y : ℝ)) := by
    simpa [sqrtInput] using RationalEnclosure.contains_point (1 - y)
  have hsqrt := certificate.sqrtOneSub.sound hparts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [lowerProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hadd := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hadd
    simpa [upperProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hlogLower := certificate.logLowerProbability.sound terms
    hparts.2.1 hlower
  have hlogUpper := certificate.logUpperProbability.sound terms
    hparts.2.2 hupper
  have hlogDiff := RationalEnclosure.contains_sub hlogUpper hlogLower
  have hquot := RationalEnclosure.contains_div hprimeParts.2 hlogDiff hsqrt
  have hscaled := RationalEnclosure.contains_scale (1 / 4 : ℚ) hquot
  let z := Real.sqrt (1 - (y : ℝ))
  have hzPos : 0 < z := Real.sqrt_pos.2 (by exact_mod_cast sub_pos.mpr hy.2)
  have hzLt : z < 1 := by
    have harg : (1 - (y : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      have hargRat : (1 - y : ℚ) ∈ Ioo 0 1 := by
        constructor <;> linarith [hy.1, hy.2]
      constructor
      · exact_mod_cast hargRat.1
      · exact_mod_cast hargRat.2
    simpa [z] using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
  have hpNe : (1 - z) / 2 ≠ 0 := by nlinarith
  have hqNe : (1 + z) / 2 ≠ 0 := by nlinarith
  have hlogIdentity :
      Real.log ((1 + z) / 2) - Real.log ((1 - z) / 2) =
        2 * Real.artanh z := by
    rw [Real.artanh_eq_half_log ⟨by linarith, hzLt.le⟩]
    rw [← Real.log_div hqNe hpNe]
    field_simp
  have hvalue :
      (1 / 4 : ℝ) *
          ((Real.log ((1 + z) / 2) - Real.log ((1 - z) / 2)) / z) =
        lrCertificateQPrime (y : ℝ) := by
    rw [lrCertificateQPrime_eq]
    change (1 / 4 : ℝ) *
        ((Real.log ((1 + z) / 2) - Real.log ((1 - z) / 2)) / z) =
      Real.artanh z / (2 * z)
    rw [hlogIdentity]
    field_simp [hzPos.ne']
    ring
  dsimp [z] at hvalue
  rw [← hvalue]
  simpa [primeEnclosure] using hscaled

end LRQPointCertificate

/-- Endpoint certificates for an entire rational interval in `0 < y < 1`. -/
structure LRQIntervalCertificate where
  lower : LRQPointCertificate
  upper : LRQPointCertificate

namespace LRQIntervalCertificate

def check (input : RationalEnclosure)
    (certificate : LRQIntervalCertificate) : Bool :=
  decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) &&
    certificate.lower.check input.lower && certificate.upper.check input.upper

def enclosure (terms : ℕ) (certificate : LRQIntervalCertificate) :
    RationalEnclosure :=
  ⟨(certificate.lower.enclosure terms).lower,
    (certificate.upper.enclosure terms).upper⟩

theorem sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.enclosure terms).Contains (lrCertificateQ y) := by
  have hraw :
      (decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
          input.upper < 1) = true ∧
        certificate.lower.check input.lower = true) ∧
      certificate.upper.check input.upper = true := by
    simpa [check] using hcheck
  have hdomain :
      (0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
        input.upper < 1 := by
    simpa using hraw.1.1
  have hlower := certificate.lower.sound terms hraw.1.2
  have hupper := certificate.upper.sound terms hraw.2
  have hlowerMem : (input.lower : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hdomain.1
    · exact_mod_cast hdomain.2.1.trans_lt hdomain.2.2
  have hupperMem : (input.upper : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hdomain.1.trans_le hdomain.2.1
    · exact_mod_cast hdomain.2.2
  have hyMem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hlowerMem.1.trans_le hy.1, hy.2.trans_lt hupperMem.2⟩
  have hmonoLower :
      lrCertificateQ (input.lower : ℝ) ≤ lrCertificateQ y :=
    lrCertificateQ_strictMonoOn.monotoneOn hlowerMem hyMem hy.1
  have hmonoUpper :
      lrCertificateQ y ≤ lrCertificateQ (input.upper : ℝ) :=
    lrCertificateQ_strictMonoOn.monotoneOn hyMem hupperMem hy.2
  exact ⟨hlower.1.trans hmonoLower, hmonoUpper.trans hupper.2⟩

end LRQIntervalCertificate

/-- Endpoint payloads for enclosing the decreasing function `Q'`. -/
structure LRQPrimeIntervalCertificate where
  lowerEndpoint : LRQPointCertificate
  upperEndpoint : LRQPointCertificate

namespace LRQPrimeIntervalCertificate

def check (input : RationalEnclosure)
    (certificate : LRQPrimeIntervalCertificate) : Bool :=
  decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) &&
    certificate.lowerEndpoint.primeCheck input.lower &&
    certificate.upperEndpoint.primeCheck input.upper

def enclosure (terms : ℕ) (certificate : LRQPrimeIntervalCertificate) :
    RationalEnclosure :=
  ⟨(certificate.upperEndpoint.primeEnclosure terms).lower,
    (certificate.lowerEndpoint.primeEnclosure terms).upper⟩

theorem sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQPrimeIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.enclosure terms).Contains (lrCertificateQPrime y) := by
  have hraw :
      (decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
          input.upper < 1) = true ∧
        certificate.lowerEndpoint.primeCheck input.lower = true) ∧
      certificate.upperEndpoint.primeCheck input.upper = true := by
    simpa [check] using hcheck
  have hdomain :
      (0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
        input.upper < 1 := by
    simpa using hraw.1.1
  have hlowerMem : input.lower ∈ Ioo (0 : ℚ) 1 :=
    ⟨hdomain.1, hdomain.2.1.trans_lt hdomain.2.2⟩
  have hupperMem : input.upper ∈ Ioo (0 : ℚ) 1 :=
    ⟨hdomain.1.trans_le hdomain.2.1, hdomain.2.2⟩
  have hlower := certificate.lowerEndpoint.prime_sound terms
    hlowerMem hraw.1.2
  have hupper := certificate.upperEndpoint.prime_sound terms
    hupperMem hraw.2
  have hlowerMemReal : (input.lower : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hlowerMem.1
    · exact_mod_cast hlowerMem.2
  have hupperMemReal : (input.upper : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hupperMem.1
    · exact_mod_cast hupperMem.2
  have hyMem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hlowerMemReal.1.trans_le hy.1, hy.2.trans_lt hupperMemReal.2⟩
  have hantiLower :
      lrCertificateQPrime (input.upper : ℝ) ≤ lrCertificateQPrime y :=
    lrCertificateQPrime_antitoneOn hyMem hupperMemReal hy.2
  have hantiUpper :
      lrCertificateQPrime y ≤ lrCertificateQPrime (input.lower : ℝ) :=
    lrCertificateQPrime_antitoneOn hlowerMemReal hyMem hy.1
  exact ⟨hupper.1.trans hantiLower, hantiUpper.trans hlower.2⟩

end LRQPrimeIntervalCertificate

/-- Executable domain check for the universal `(C3)` enclosure of `Q''`. -/
def lrQSecondCoarseCheck (input : RationalEnclosure) : Bool :=
  decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1)

/-- The universal rational enclosure `-1/(4y₀) ≤ Q''(y) ≤ 0` on an
interval whose lower endpoint is `y₀ > 0`. -/
def lrQSecondCoarseEnclosure (input : RationalEnclosure) : RationalEnclosure :=
  ⟨-1 / (4 * input.lower), 0⟩

theorem lrQSecondCoarseEnclosure_sound {input : RationalEnclosure}
    (hcheck : lrQSecondCoarseCheck input = true)
    {y : ℝ} (hy : input.Contains y) :
    (lrQSecondCoarseEnclosure input).Contains (lrCertificateQSecond y) := by
  have hdomain :
      (0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
        input.upper < 1 := by
    simpa [lrQSecondCoarseCheck] using hcheck
  have hlowerPos : (0 : ℝ) < (input.lower : ℝ) := by
    exact_mod_cast hdomain.1
  have hupperLt : (input.upper : ℝ) < 1 := by
    exact_mod_cast hdomain.2.2
  have hyMem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hlowerPos.trans_le hy.1, hy.2.trans_lt hupperLt⟩
  have hdenLe : 4 * (input.lower : ℝ) ≤ 4 * y :=
    mul_le_mul_of_nonneg_left hy.1 (by norm_num)
  have hinv : 1 / (4 * y) ≤ 1 / (4 * (input.lower : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hdenLe
  have hcoarse :
      -1 / (4 * (input.lower : ℝ)) ≤ -1 / (4 * y) := by
    have := neg_le_neg hinv
    simpa only [neg_div] using this
  have hlower := hcoarse.trans (lrCertificateQSecond_lower hyMem)
  have hupper := lrCertificateQSecond_nonpos hyMem
  unfold lrQSecondCoarseEnclosure RationalEnclosure.Contains
  norm_num at ⊢
  exact ⟨hlower, hupper⟩

end CourtadeKumar
