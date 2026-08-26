import InformationTheory.CourtadeKumar.LRAbelSummation

/-! Assembly of all finite prefixes in the base (`R = 0`) Abel argument. -/

open Set Finset
open scoped BigOperators

namespace CourtadeKumar

/-- The complete prefix sequence used in the audited base Abel argument.
Index zero is the exceptional first prefix; subsequent indices use `S_N`. -/
noncomputable def lrAbelBasePrefix (v : ℝ) : ℕ → ℝ
  | 0 => lrAbelFirstPrefix v
  | n + 1 => lrAbelPrefixS (n + 2) v

/-- Coefficients recovered from their audited prefixes.  The separate first
coefficient reflects the manuscript's separate formula for `S_1`. -/
noncomputable def lrAbelBaseCoeff (v : ℝ) : ℕ → ℝ
  | 0 => lrAbelBasePrefix v 0
  | n + 1 => lrAbelBasePrefix v (n + 1) - lrAbelBasePrefix v n

lemma lrAbelBaseCoeff_zero (v : ℝ) :
    lrAbelBaseCoeff v 0 = lrAbelBasePrefix v 0 := by
  rfl

lemma lrAbelBaseCoeff_succ (v : ℝ) (n : ℕ) :
    lrAbelBaseCoeff v (n + 1) =
      lrAbelBasePrefix v (n + 1) - lrAbelBasePrefix v n := by
  rfl

/-- The recovered coefficients have exactly the intended finite prefixes. -/
theorem lrSeriesPrefix_lrAbelBaseCoeff (v : ℝ) (n : ℕ) :
    lrSeriesPrefix (lrAbelBaseCoeff v) n = lrAbelBasePrefix v n := by
  induction n with
  | zero => simp [lrSeriesPrefix_zero, lrAbelBaseCoeff_zero]
  | succ n ih =>
      have hstep := lrSeriesPrefix_succ_sub (lrAbelBaseCoeff v) n
      rw [lrAbelBaseCoeff_succ] at hstep
      linarith

/-- Every finite base Abel prefix is strictly positive in the open physical
`v`-range, combining the exceptional first-prefix proof with the uniform
quantitative estimate for all later prefixes. -/
theorem lrAbelBasePrefix_pos
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (n : ℕ) :
    0 < lrAbelBasePrefix v n := by
  cases n with
  | zero => exact lrAbelFirstPrefix_pos hv
  | succ n =>
      have hN : 2 ≤ n + 2 := by omega
      have hden : 0 < 4 * ((n + 2 : ℕ) : ℝ) * (2 * ((n + 2 : ℕ) : ℝ) + 1) := by
        positivity
      by_cases hveq : v = 1
      · subst v
        have hlower := lrAbelPrefixS_one_lower_of_tail hN
          (lrAbelTailValue_bound (show 1 ≤ n + 2 by omega))
        exact lt_of_lt_of_le (div_pos (by norm_num) hden) hlower
      · have hvOpen : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, lt_of_le_of_ne hv.2 hveq⟩
        have hlower := lrAbelPrefixS_quantitative_lower hN hvOpen
        have hpow : 0 < v ^ (2 * (n + 2) + 1) := pow_pos hv.1 _
        exact lt_of_lt_of_le (div_pos hpow hden) hlower

theorem lrAbelBasePrefix_nonneg
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ lrSeriesPrefix (lrAbelBaseCoeff v) n := by
  rw [lrSeriesPrefix_lrAbelBaseCoeff]
  exact (lrAbelBasePrefix_pos hv n).le

end CourtadeKumar
