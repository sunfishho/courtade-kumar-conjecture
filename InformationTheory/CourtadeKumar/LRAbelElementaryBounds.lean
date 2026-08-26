import InformationTheory.CourtadeKumar.LRAbelPrefixBounds

/-! Elementary scalar bounds used in the audited base Abel-prefix argument. -/

open Set

namespace CourtadeKumar

theorem lr_log_one_add_lower
    {v : ℝ} (hv : 0 ≤ v) :
    2 * v / (2 + v) ≤ Real.log (1 + v) := by
  simpa [add_comm] using Real.le_log_one_add_of_nonneg hv

lemma lr_one_third_cubic_bound
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    v - v ^ 2 + v ^ 3 / 3 ≤ 1 / 3 := by
  have hcube : 0 ≤ (1 - v) ^ 3 := pow_nonneg (sub_nonneg.mpr hv.2) _
  nlinarith

lemma lr_log_two_lt_three_quarters :
    Real.log 2 < 3 / 4 := by
  linarith [Real.log_two_lt_d9]

lemma lr_first_prefix_margin_pos :
    0 < 3 / 2 - 2 * Real.log 2 := by
  linarith [lr_log_two_lt_three_quarters]

lemma lr_reciprocal_tail_decomposition
    {y : ℝ} (hy : y ≠ -1) :
    1 / (1 + y) =
      1 / 2 + (1 - y) / 4 + (1 - y) ^ 2 / (4 * (1 + y)) := by
  have hden : 1 + y ≠ 0 := by
    intro h
    apply hy
    linarith
  field_simp [hden]
  ring

/-- The final rational estimate in the manuscript's bound for `T_N`. -/
theorem lr_abel_tail_rational_bound
    {N : ℕ} (hN : 1 ≤ N) :
    1 / (2 * (2 * (N : ℝ) + 1)) +
        1 / (4 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) +
        1 / (2 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2) *
          (2 * (N : ℝ) + 3)) ≤
      (4 * (N : ℝ) + 1) /
        (8 * (N : ℝ) * (2 * (N : ℝ) + 1)) := by
  have hNReal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNReal
  have h1 : 0 < 2 * (N : ℝ) + 1 := by positivity
  have h2 : 0 < 2 * (N : ℝ) + 2 := by positivity
  have h3 : 0 < 2 * (N : ℝ) + 3 := by positivity
  field_simp [hNpos.ne', h1.ne', h2.ne', h3.ne']
  nlinarith

end CourtadeKumar
