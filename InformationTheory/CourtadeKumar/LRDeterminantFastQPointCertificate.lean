import InformationTheory.CourtadeKumar.LRDeterminantAutoCertificateCorrectness
import InformationTheory.CourtadeKumar.LRCertificateQEnclosure

/-!
# Fast point certificates for the small upper-`K` range

On the authenticated upper-`K` boxes every positive argument of `Q` is at
most `1/16`.  A fixed sixth-order binomial enclosure for `sqrt (1-y)` is
therefore both much faster and more accurate than forty rational bisections.
The two square inequalities below are proved once; concrete point checks only
perform logarithm range reduction.
-/

namespace CourtadeKumar
namespace LRQFastPointCertificate

open Set

def sqrtUpper (y : ℚ) : ℚ :=
  1 - y / 2 - y ^ 2 / 8 - y ^ 3 / 16 -
    5 * y ^ 4 / 128 - 7 * y ^ 5 / 256 - 21 * y ^ 6 / 1024

def sqrtLower (y : ℚ) : ℚ := sqrtUpper y - y ^ 7 / 32

def sqrtCertificate (y : ℚ) : RationalEnclosure.SqrtCertificate :=
  { lower := sqrtLower y, upper := sqrtUpper y }

private theorem pow_le_self {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) : y ^ n ≤ y := by
  simpa using pow_le_pow_of_le_one hy0 hy1 hn

theorem sqrtLower_nonneg {y : ℚ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 16) :
    0 ≤ sqrtLower y := by
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have h2 := pow_le_self hy0 hy1 2 (by omega)
  have h3 := pow_le_self hy0 hy1 3 (by omega)
  have h4 := pow_le_self hy0 hy1 4 (by omega)
  have h5 := pow_le_self hy0 hy1 5 (by omega)
  have h6 := pow_le_self hy0 hy1 6 (by omega)
  have h7 := pow_le_self hy0 hy1 7 (by omega)
  unfold sqrtLower sqrtUpper
  nlinarith

theorem sqrtLower_sq_le {y : ℚ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 16) :
    sqrtLower y ^ 2 ≤ 1 - y := by
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have h2 := pow_le_self hy0 hy1 2 (by omega)
  have h3 := pow_le_self hy0 hy1 3 (by omega)
  have h4 := pow_le_self hy0 hy1 4 (by omega)
  have h5 := pow_le_self hy0 hy1 5 (by omega)
  have h6 := pow_le_self hy0 hy1 6 (by omega)
  have h7 := pow_le_self hy0 hy1 7 (by omega)
  have hcoefficient :
      0 ≤ 31744 - (43328 * y + 13120 * y ^ 2 + 6560 * y ^ 3 +
        3736 * y ^ 4 + 2233 * y ^ 5 + 1344 * y ^ 6 + 1024 * y ^ 7) := by
    nlinarith
  have hidentity :
      (1 - y) - sqrtLower y ^ 2 =
        y ^ 7 * (31744 - (43328 * y + 13120 * y ^ 2 +
          6560 * y ^ 3 + 3736 * y ^ 4 + 2233 * y ^ 5 +
          1344 * y ^ 6 + 1024 * y ^ 7)) / 1048576 := by
    unfold sqrtLower sqrtUpper
    ring
  rw [← sub_nonneg]
  rw [hidentity]
  positivity

theorem sqrtUpper_nonneg {y : ℚ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 16) :
    0 ≤ sqrtUpper y := by
  have hlower := sqrtLower_nonneg hy0 hy
  have htail : 0 ≤ y ^ 7 / 32 := by positivity
  unfold sqrtLower at hlower
  linarith

theorem le_sqrtUpper_sq {y : ℚ} (hy0 : 0 ≤ y) :
    1 - y ≤ sqrtUpper y ^ 2 := by
  have hidentity :
      sqrtUpper y ^ 2 - (1 - y) =
        y ^ 7 * (33792 + 10560 * y + 4928 * y ^ 2 +
          2464 * y ^ 3 + 1176 * y ^ 4 + 441 * y ^ 5) / 1048576 := by
    unfold sqrtUpper
    ring
  rw [← sub_nonneg]
  rw [hidentity]
  positivity

theorem sqrtCertificate_check {y : ℚ}
    (hy0 : 0 ≤ y) (hy : y ≤ 1 / 16) :
    (sqrtCertificate y).check (LRQPointCertificate.sqrtInput y) = true := by
  simp only [RationalEnclosure.SqrtCertificate.check, decide_eq_true_eq]
  change 0 ≤ 1 - y ∧ 1 - y ≤ 1 - y ∧
    0 ≤ sqrtLower y ∧ sqrtLower y ^ 2 ≤ 1 - y ∧
    0 ≤ sqrtUpper y ∧ 1 - y ≤ sqrtUpper y ^ 2
  exact ⟨by linarith, le_rfl, sqrtLower_nonneg hy0 hy,
    sqrtLower_sq_le hy0 hy, sqrtUpper_nonneg hy0 hy,
    le_sqrtUpper_sq hy0⟩

def auto (logFuel : ℕ) (y : ℚ) : LRQPointCertificate :=
  let sqrtOneSub := sqrtCertificate y
  let seed : LRQPointCertificate :=
    { sqrtOneSub := sqrtOneSub
      logLowerProbability :=
        { lower := { exponent := 0, mantissa := 0 }
          upper := { exponent := 0, mantissa := 0 } }
      logUpperProbability :=
        { lower := { exponent := 0, mantissa := 0 }
          upper := { exponent := 0, mantissa := 0 } } }
  { sqrtOneSub := sqrtOneSub
    logLowerProbability :=
      RationalEnclosure.autoLogIntervalCertificate logFuel
        seed.lowerProbability
    logUpperProbability :=
      RationalEnclosure.autoLogIntervalCertificate logFuel
        seed.upperProbability }

def autoPrimeSucceeds (logFuel : ℕ) (y : ℚ) : Bool :=
  let certificate := auto logFuel y
  RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
      certificate.lowerProbability &&
    RationalEnclosure.autoLogIntervalCertificateSucceeds logFuel
      certificate.upperProbability

theorem auto_primeCheck_of_succeeds (logFuel : ℕ) {y : ℚ}
    (hy0 : 0 ≤ y) (hy : y ≤ 1 / 16)
    (hsucceeds : autoPrimeSucceeds logFuel y = true) :
    (auto logFuel y).primeCheck y = true := by
  simp only [autoPrimeSucceeds, Bool.and_eq_true] at hsucceeds
  have hsqrt := sqrtCertificate_check hy0 hy
  have hlower :=
    RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (auto logFuel y).lowerProbability hsucceeds.1
  have hupper :=
    RationalEnclosure.autoLogIntervalCertificate_check_of_succeeds
      logFuel (auto logFuel y).upperProbability hsucceeds.2
  have hsqrtLower : 0 < (auto logFuel y).sqrtEnclosure.lower := by
    change 0 < sqrtLower y
    have hnonneg := sqrtLower_nonneg hy0 hy
    have hstrict : 0 < (1 : ℚ) - 71345 / 16 / 65536 := by norm_num
    have hy1 : y ≤ 1 := hy.trans (by norm_num)
    have h2 := pow_le_self hy0 hy1 2 (by omega)
    have h3 := pow_le_self hy0 hy1 3 (by omega)
    have h4 := pow_le_self hy0 hy1 4 (by omega)
    have h5 := pow_le_self hy0 hy1 5 (by omega)
    have h6 := pow_le_self hy0 hy1 6 (by omega)
    have h7 := pow_le_self hy0 hy1 7 (by omega)
    unfold sqrtLower sqrtUpper
    nlinarith
  simp only [LRQPointCertificate.primeCheck, LRQPointCertificate.check,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨by simpa [auto] using hsqrt, hlower⟩, hupper⟩,
    hsqrtLower⟩

end LRQFastPointCertificate
end CourtadeKumar
