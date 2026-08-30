import InformationTheory.CourtadeKumar.LRCertificateQ
import InformationTheory.CourtadeKumar.LRCertificateQPointSound

/-!
# Executable endpoint enclosures for the LR entropy scalar

The external generator supplies only range-reduction and square-root data.
Lean checks those data, reconstructs the binary-entropy expression using exact
rational interval arithmetic, and proves that the resulting interval contains
the actual `lrCertificateQ` value.
-/

open Set

namespace CourtadeKumar

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

/-- A value-only enclosure for nonnegative intervals near zero.  The
derivative of `Q` is singular at zero, but `Q` itself is continuous and
nonnegative.  Endpoint-facing value evaluators can use this certificate
without pretending that a finite `Q'` enclosure exists. -/
structure LRQZeroIntervalCertificate where
  upper : LRQPointCertificate
  sqrtUpper : RationalEnclosure.SqrtCertificate

namespace LRQZeroIntervalCertificate

def check (input : RationalEnclosure)
    (certificate : LRQZeroIntervalCertificate) : Bool :=
  decide (0 ≤ input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) &&
    if input.upper = 0 then true
    else certificate.upper.check input.upper ||
      certificate.sqrtUpper.check (RationalEnclosure.point input.upper)

def enclosure (terms : ℕ) (input : RationalEnclosure)
    (certificate : LRQZeroIntervalCertificate) : RationalEnclosure :=
  if input.upper = 0 then RationalEnclosure.point 0
  else if certificate.upper.check input.upper then
    ⟨0, (certificate.upper.enclosure terms).upper⟩
  else ⟨0, 2 * certificate.sqrtUpper.upper⟩

theorem sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQZeroIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.enclosure terms input).Contains (lrCertificateQ y) := by
  have hparts :
      decide (0 ≤ input.lower ∧ input.lower ≤ input.upper ∧
          input.upper < 1) = true ∧
        (if input.upper = 0 then true
          else certificate.upper.check input.upper ||
            certificate.sqrtUpper.check
              (RationalEnclosure.point input.upper)) = true := by
    simpa [check] using hcheck
  have hdomain : (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1 := by
    simpa using hparts.1
  by_cases hu0 : input.upper = 0
  · have hy0 : y = 0 := by
      have hinputLower : (0 : ℝ) ≤ (input.lower : ℝ) := by
        exact_mod_cast hdomain.1
      have hlo : (0 : ℝ) ≤ y := hinputLower.trans hy.1
      have hup : y ≤ (0 : ℝ) := by simpa [hu0] using hy.2
      linarith
    subst y
    simp [enclosure, hu0, RationalEnclosure.point,
      RationalEnclosure.Contains]
  · have huNonneg : (0 : ℚ) ≤ input.upper :=
      hdomain.1.trans hdomain.2.1
    have huPos : (0 : ℚ) < input.upper :=
      lt_of_le_of_ne huNonneg (Ne.symm hu0)
    have huMem : (input.upper : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact_mod_cast huPos
      · exact_mod_cast hdomain.2.2
    have hyMemClosed : y ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have hinputLower : (0 : ℝ) ≤ (input.lower : ℝ) := by
          exact_mod_cast hdomain.1
        exact hinputLower.trans hy.1
      · exact hy.2.trans huMem.2.le
    have hlower : 0 ≤ lrCertificateQ y :=
      lrCertificateQ_nonneg hyMemClosed
    by_cases hpoint : certificate.upper.check input.upper = true
    · have hupper := certificate.upper.sound terms hpoint
      have hupperValue :
          lrCertificateQ y ≤
            ((certificate.upper.enclosure terms).upper : ℝ) := by
        by_cases hy0 : y = 0
        · subst y
          rw [lrCertificateQ_zero]
          exact (lrCertificateQ_nonneg
            ⟨huMem.1.le, huMem.2.le⟩).trans hupper.2
        · have hyPos : 0 < y :=
            lt_of_le_of_ne hyMemClosed.1 (Ne.symm hy0)
          have hyMem : y ∈ Ioo (0 : ℝ) 1 :=
            ⟨hyPos, hy.2.trans_lt huMem.2⟩
          have hmono : lrCertificateQ y ≤
              lrCertificateQ (input.upper : ℝ) :=
            lrCertificateQ_strictMonoOn.monotoneOn hyMem huMem hy.2
          exact hmono.trans hupper.2
      simpa [enclosure, hu0, hpoint, RationalEnclosure.Contains] using
        And.intro hlower hupperValue
    · have hpointFalse : certificate.upper.check input.upper = false :=
        Bool.eq_false_of_not_eq_true hpoint
      have hsqrtCheck : certificate.sqrtUpper.check
          (RationalEnclosure.point input.upper) = true := by
        simpa [hu0, hpointFalse] using hparts.2
      have hsqrt := certificate.sqrtUpper.sound hsqrtCheck
        (RationalEnclosure.contains_point input.upper)
      have hsqrtMono : Real.sqrt y ≤ Real.sqrt (input.upper : ℝ) :=
        Real.sqrt_le_sqrt hy.2
      have hQUpper : lrCertificateQ y ≤
          2 * (certificate.sqrtUpper.upper : ℝ) := calc
        lrCertificateQ y ≤ 2 * Real.sqrt y :=
          lrCertificateQ_le_two_sqrt hyMemClosed
        _ ≤ 2 * Real.sqrt (input.upper : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrtMono (by norm_num)
        _ ≤ 2 * (certificate.sqrtUpper.upper : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt.2 (by norm_num)
      simpa [enclosure, hu0, hpointFalse,
        RationalEnclosure.Contains] using And.intro hlower hQUpper

/-- The same endpoint payload also encloses the regularized derivative
factor `y * Q'(y)`.  Concavity puts this factor between `0` and `Q(y)`, so
no logarithm or derivative enclosure at `y = 0` is required. -/
theorem mul_prime_sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQZeroIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.enclosure terms input).Contains
      (y * lrCertificateQPrime y) := by
  have hdomain : (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1 := by
    have hparts :
        decide (0 ≤ input.lower ∧ input.lower ≤ input.upper ∧
            input.upper < 1) = true ∧
          (if input.upper = 0 then true
            else certificate.upper.check input.upper ||
              certificate.sqrtUpper.check
                (RationalEnclosure.point input.upper)) = true := by
      simpa [check] using hcheck
    simpa using hparts.1
  have hyNonneg : (0 : ℝ) ≤ y := by
    have hlower : (0 : ℝ) ≤ (input.lower : ℝ) := by
      exact_mod_cast hdomain.1
    exact hlower.trans hy.1
  have hyLt : y < 1 := by
    have hupper : (input.upper : ℝ) < 1 := by
      exact_mod_cast hdomain.2.2
    exact hy.2.trans_lt hupper
  have hregular := lrCertificateQ_mul_prime_mem ⟨hyNonneg, hyLt⟩
  have hq := certificate.sound terms hcheck hy
  have hlower : (certificate.enclosure terms input).lower = 0 := by
    simp only [enclosure]
    split
    · rfl
    · split <;> rfl
  exact ⟨by rw [hlower]; simpa using hregular.1,
    hregular.2.trans hq.2⟩

end LRQZeroIntervalCertificate

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
