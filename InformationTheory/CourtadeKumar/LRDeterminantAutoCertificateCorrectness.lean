import InformationTheory.CourtadeKumar.LRDeterminantAutoCertificateCore

/-!
# Correctness of deterministic elementary certificates

This module proves that the executable square-root and logarithm certificate
constructors produce certificates accepted by their original checkers whenever
small, structurally equivalent success predicates hold.
-/

namespace CourtadeKumar
namespace RationalEnclosure

theorem sqrtBracket_spec (fuel : ℕ) {x lo hi : ℚ}
    (hlo : 0 ≤ lo) (hloSq : lo ^ 2 ≤ x)
    (hhi : 0 ≤ hi) (hhiSq : x ≤ hi ^ 2) :
    let result := sqrtBracket fuel x lo hi
    0 ≤ result.1 ∧ result.1 ^ 2 ≤ x ∧
      0 ≤ result.2 ∧ x ≤ result.2 ^ 2 := by
  induction fuel generalizing lo hi with
  | zero =>
      simp [sqrtBracket, hlo, hloSq, hhi, hhiSq]
  | succ fuel ih =>
      simp only [sqrtBracket]
      split_ifs with hmid
      · apply ih
        · linarith
        · exact hmid
        · exact hhi
        · exact hhiSq
      · apply ih
        · exact hlo
        · exact hloSq
        · linarith
        · exact le_of_not_ge hmid

theorem autoSqrtCertificate_check
    {input : RationalEnclosure}
    (hlower : 0 ≤ input.lower)
    (hordered : input.lower ≤ input.upper) (fuel : ℕ) :
    (autoSqrtCertificate fuel input).check input = true := by
  let lowerBracket := sqrtBracket fuel input.lower 0 (max 1 input.lower)
  let upperBracket := sqrtBracket fuel input.upper 0 (max 1 input.upper)
  have hlowerUpperNonnegative : (0 : ℚ) ≤ max 1 input.lower := by
    exact le_trans zero_le_one (le_max_left 1 input.lower)
  have hupperUpperNonnegative : (0 : ℚ) ≤ max 1 input.upper := by
    exact le_trans zero_le_one (le_max_left 1 input.upper)
  have hlowerUpperSq : input.lower ≤ (max 1 input.lower) ^ 2 := by
    rcases le_total input.lower 1 with hle | hge
    · rw [max_eq_left hle]
      linarith
    · rw [max_eq_right hge]
      nlinarith
  have hupperNonnegative : (0 : ℚ) ≤ input.upper := hlower.trans hordered
  have hupperUpperSq : input.upper ≤ (max 1 input.upper) ^ 2 := by
    rcases le_total input.upper 1 with hle | hge
    · rw [max_eq_left hle]
      linarith
    · rw [max_eq_right hge]
      nlinarith
  have hlowerSpec :
      0 ≤ lowerBracket.1 ∧ lowerBracket.1 ^ 2 ≤ input.lower ∧
        0 ≤ lowerBracket.2 ∧ input.lower ≤ lowerBracket.2 ^ 2 := by
    simpa [lowerBracket] using
      (sqrtBracket_spec fuel (x := input.lower) (lo := 0)
        (hi := max 1 input.lower) (by norm_num) (by simpa using hlower)
        hlowerUpperNonnegative hlowerUpperSq)
  have hupperSpec :
      0 ≤ upperBracket.1 ∧ upperBracket.1 ^ 2 ≤ input.upper ∧
        0 ≤ upperBracket.2 ∧ input.upper ≤ upperBracket.2 ^ 2 := by
    simpa [upperBracket] using
      (sqrtBracket_spec fuel (x := input.upper) (lo := 0)
        (hi := max 1 input.upper) (by norm_num)
        (by simpa using hupperNonnegative)
        hupperUpperNonnegative hupperUpperSq)
  simp only [SqrtCertificate.check, autoSqrtCertificate, decide_eq_true_eq]
  exact ⟨hlower, hordered, hlowerSpec.1, hlowerSpec.2.1,
    hupperSpec.2.2.1, hupperSpec.2.2.2⟩

theorem autoLogRangeCertificate_identity (fuel : ℕ) (x : ℚ) :
    let certificate := autoLogRangeCertificate fuel x
    x = (2 : ℚ) ^ certificate.exponent * certificate.mantissa := by
  induction fuel generalizing x with
  | zero =>
      simp [autoLogRangeCertificate]
  | succ fuel ih =>
      rw [autoLogRangeCertificate]
      split_ifs with hxLower hxMiddle
      · let child := autoLogRangeCertificate fuel (2 * x)
        change x = (2 : ℚ) ^ (child.exponent - 1) * child.mantissa
        have hchild :
            2 * x = (2 : ℚ) ^ child.exponent * child.mantissa := by
          simpa [child] using ih (2 * x)
        calc
          x = (2 * x) / 2 := by ring
          _ = ((2 : ℚ) ^ child.exponent * child.mantissa) / 2 := by
            rw [hchild]
          _ = (2 : ℚ) ^ (child.exponent - 1) * child.mantissa := by
            rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
            norm_num
            ring
      · simp
      · let child := autoLogRangeCertificate fuel (x / 2)
        change x = (2 : ℚ) ^ (child.exponent + 1) * child.mantissa
        have hchild :
            x / 2 = (2 : ℚ) ^ child.exponent * child.mantissa := by
          simpa [child] using ih (x / 2)
        calc
          x = 2 * (x / 2) := by ring
          _ = 2 * ((2 : ℚ) ^ child.exponent * child.mantissa) := by
            rw [hchild]
          _ = (2 : ℚ) ^ (child.exponent + 1) * child.mantissa := by
            rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
            norm_num
            ring

/-- Cheap executable fuel test for the deterministic logarithm normalizer.
Unlike the final certificate checker, this follows only the normalization
branches; the exact power-of-two identity is proved once above. -/
def autoLogRangeCertificateSucceeds : ℕ → ℚ → Bool
  | 0, x => decide ((1 : ℚ) ≤ x ∧ x < 2)
  | fuel + 1, x =>
      if x < 1 then
        autoLogRangeCertificateSucceeds fuel (2 * x)
      else if x < 2 then
        true
      else
        autoLogRangeCertificateSucceeds fuel (x / 2)

theorem autoLogRangeCertificate_normalized_of_succeeds
    (fuel : ℕ) (x : ℚ)
    (hsucceeds : autoLogRangeCertificateSucceeds fuel x = true) :
    let certificate := autoLogRangeCertificate fuel x
    (1 : ℚ) ≤ certificate.mantissa ∧ certificate.mantissa < 2 := by
  induction fuel generalizing x with
  | zero =>
      simpa [autoLogRangeCertificateSucceeds, autoLogRangeCertificate]
        using hsucceeds
  | succ fuel ih =>
      by_cases hxLower : x < 1
      · simp only [autoLogRangeCertificateSucceeds, hxLower, if_pos]
          at hsucceeds
        rw [autoLogRangeCertificate]
        simp only [hxLower, if_pos]
        exact ih (2 * x) hsucceeds
      · have hxOne : (1 : ℚ) ≤ x := le_of_not_gt hxLower
        by_cases hxUpper : x < 2
        · rw [autoLogRangeCertificate]
          simp [hxLower, hxUpper, hxOne]
        · simp only [autoLogRangeCertificateSucceeds, hxLower, if_false,
            hxUpper] at hsucceeds
          rw [autoLogRangeCertificate]
          simp only [hxLower, if_false, hxUpper]
          exact ih (x / 2) hsucceeds

theorem autoLogRangeCertificate_check_of_succeeds
    (fuel : ℕ) (x : ℚ)
    (hsucceeds : autoLogRangeCertificateSucceeds fuel x = true) :
    (autoLogRangeCertificate fuel x).check x = true := by
  simp only [LogRangeCertificate.check, decide_eq_true_eq]
  exact ⟨
    (autoLogRangeCertificate_normalized_of_succeeds fuel x hsucceeds).1,
    (autoLogRangeCertificate_normalized_of_succeeds fuel x hsucceeds).2,
    autoLogRangeCertificate_identity fuel x⟩

def autoLogIntervalCertificateSucceeds (fuel : ℕ)
    (input : RationalEnclosure) : Bool :=
  decide ((0 : ℚ) < input.lower) &&
    (autoLogRangeCertificateSucceeds fuel input.lower &&
      autoLogRangeCertificateSucceeds fuel input.upper)

theorem autoLogIntervalCertificate_check_of_succeeds
    (fuel : ℕ) (input : RationalEnclosure)
    (hsucceeds : autoLogIntervalCertificateSucceeds fuel input = true) :
    (autoLogIntervalCertificate fuel input).check input = true := by
  simp only [autoLogIntervalCertificateSucceeds, Bool.and_eq_true,
    decide_eq_true_eq] at hsucceeds
  simp only [LogIntervalCertificate.check, autoLogIntervalCertificate,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hsucceeds.1,
    autoLogRangeCertificate_check_of_succeeds fuel input.lower
      hsucceeds.2.1,
    autoLogRangeCertificate_check_of_succeeds fuel input.upper
      hsucceeds.2.2⟩

end RationalEnclosure
end CourtadeKumar
