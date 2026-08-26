import InformationTheory.CourtadeKumar.LRAbelPrefixCanonical

/-! The quantitative derivative bound for the audited Abel prefixes. -/

open Set

namespace CourtadeKumar

noncomputable def lrAbelPrefixSUpper (N : ℕ) (v : ℝ) : ℝ :=
  (2 * v / (2 + v)) * (v ^ 2 - 1) / v ^ 2 - 1 +
    (1 - v ^ 2) / v ^ 2 *
      (v ^ 2 * (1 - v ^ (2 * N - 2)) / (2 * (1 - v ^ 2))) +
    v ^ (2 * N - 2) / (2 * (N : ℝ)) +
    (1 - v) *
      (v * (1 - v ^ (2 * N - 2)) / (1 - v ^ 2)) -
    (1 - v) / (1 + v) -
    v ^ (2 * N) / (4 * (N : ℝ)) +
    (3 - v) * v ^ (2 * N - 1) / 2

theorem lrAbelPrefixSCanonical_le_upper
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrAbelPrefixSCanonical N v ≤ lrAbelPrefixSUpper N v := by
  have hv2pos : 0 < v ^ 2 := sq_pos_of_pos hv.1
  have hfactor : 0 < (1 - v) * (1 + v) :=
    mul_pos (sub_pos.mpr hv.2) (by nlinarith [hv.1])
  have hv2lt : v ^ 2 < 1 := by nlinarith [hfactor]
  have hlogCoef : (v ^ 2 - 1) / v ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv2lt.le) hv2pos.le
  have hlog := lr_log_one_add_lower hv.1.le
  have hlogTerm := mul_le_mul_of_nonpos_right hlog hlogCoef
  have hlogTerm' :
      Real.log (1 + v) * (v ^ 2 - 1) / v ^ 2 ≤
        (2 * v / (2 + v)) * (v ^ 2 - 1) / v ^ 2 := by
    calc
      _ = Real.log (1 + v) * ((v ^ 2 - 1) / v ^ 2) := by ring
      _ ≤ (2 * v / (2 + v)) * ((v ^ 2 - 1) / v ^ 2) := hlogTerm
      _ = _ := by ring
  have hpred : 1 ≤ N - 1 := by omega
  have hL := lrAbelLogPrefix_le_closed (N - 1) hv.1.le hv.2
  rw [← lrAbelLogPrefixPow_eq] at hL
  rw [show 2 * (N - 1) = 2 * N - 2 by omega] at hL
  have hLCoef : 0 ≤ (1 - v ^ 2) / v ^ 2 :=
    div_nonneg (sub_nonneg.mpr hv2lt.le) hv2pos.le
  have hLTerm := mul_le_mul_of_nonneg_left hL hLCoef
  have hC := lrAbelLogDerivPrefix_closed (N - 1) hv.1.le hv.2
  rw [show 2 * (N - 1) = 2 * N - 2 by omega] at hC
  unfold lrAbelPrefixSCanonical lrAbelPrefixSUpper
  rw [hC]
  linarith [hlogTerm', hLTerm]

theorem lrAbelPrefix_upper_gap_eq_brace
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    v ^ (2 * N) / (4 * (N : ℝ)) - lrAbelPrefixSUpper N v =
      (1 - v) /
          (2 * (N : ℝ) * v * (1 + v) * (2 + v)) *
        lrAbelPrefixBrace N v := by
  have hNOne : 1 ≤ N := by omega
  have hNReal : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNOne)
  have hv0 : v ≠ 0 := hv.1.ne'
  have hplus1 : 1 + v ≠ 0 := by nlinarith [hv.1]
  have hplus2 : 2 + v ≠ 0 := by nlinarith [hv.1]
  have hfactor : 0 < (1 - v) * (1 + v) :=
    mul_pos (sub_pos.mpr hv.2) (by nlinarith [hv.1])
  have hvSq : 1 - v ^ 2 ≠ 0 := by nlinarith [hfactor]
  have hpowOdd : v * v ^ (2 * N - 2) = v ^ (2 * N - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpowEven : v ^ 2 * v ^ (2 * N - 2) = v ^ (2 * N) := by
    rw [← pow_add]
    congr 1
    omega
  unfold lrAbelPrefixSUpper lrAbelPrefixBrace lrAbelPrefixPoly
  field_simp [hNReal.ne', hv0, hplus1, hplus2, hvSq]
  field_simp [hNReal.ne', hv0, hplus1, hplus2, hvSq]
  rw [← hpowOdd, ← hpowEven]
  ring

theorem lrAbelPrefixSDeriv_le
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrAbelPrefixSDeriv N v ≤ v ^ (2 * N) / (4 * (N : ℝ)) := by
  have hcanonical := lrAbelPrefixSCanonical_le_upper hN hv
  have hgap := lrAbelPrefix_upper_gap_eq_brace hN hv
  have hbrace := lrAbelPrefixBrace_nonneg hN ⟨hv.1.le, hv.2.le⟩
  have hprefactor : 0 ≤
      (1 - v) / (2 * (N : ℝ) * v * (1 + v) * (2 + v)) := by
    have hNReal : 0 < (N : ℝ) := by
      have hNOne : 1 ≤ N := by omega
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNOne)
    have hplus1 : 0 < 1 + v := by nlinarith [hv.1]
    have hplus2 : 0 < 2 + v := by nlinarith [hv.1]
    have hden : 0 < 2 * (N : ℝ) * v * (1 + v) * (2 + v) := by
      exact mul_pos
        (mul_pos (mul_pos (mul_pos (by norm_num) hNReal) hv.1) hplus1)
        hplus2
    exact div_nonneg (sub_nonneg.mpr hv.2.le) hden.le
  have hupper : lrAbelPrefixSUpper N v ≤
      v ^ (2 * N) / (4 * (N : ℝ)) := by
    nlinarith [mul_nonneg hprefactor hbrace]
  exact (lrAbelPrefixSDeriv_eq_canonical (le_trans (by omega) hN) hv.1).le.trans
    (hcanonical.trans hupper)

/-- The manuscript's derivative inequality for the actual prefix function. -/
theorem hasDerivAt_lrAbelPrefixS_le
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrAbelPrefixS N) (lrAbelPrefixSDeriv N v) v ∧
      lrAbelPrefixSDeriv N v ≤ v ^ (2 * N) / (4 * (N : ℝ)) :=
  ⟨hasDerivAt_lrAbelPrefixS (le_trans (by omega) hN) hv.1,
    lrAbelPrefixSDeriv_le hN hv⟩

end CourtadeKumar
