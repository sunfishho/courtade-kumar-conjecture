import InformationTheory.CourtadeKumar.LRPositiveChartAssembly

/-! Exact rational logarithm bounds used by the low-shape Bernstein
certificates. -/

open Set

namespace CourtadeKumar

noncomputable def lrAtanh5 (y : ℝ) : ℝ :=
  2 * (y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7 + y ^ 9 / 9)

noncomputable def lrAtanh5Upper (y : ℝ) : ℝ :=
  lrAtanh5 y + 2 * y ^ 11 / (11 * (1 - y ^ 2))

lemma hasDerivAt_lrAtanh5 (y : ℝ) :
    HasDerivAt lrAtanh5
      (2 * (1 + y ^ 2 + y ^ 4 + y ^ 6 + y ^ 8)) y := by
  have h := hasDerivAt_id y
  unfold lrAtanh5
  convert (((((h.add ((h.pow 3).div_const 3)).add
    ((h.pow 5).div_const 5)).add ((h.pow 7).div_const 7)).add
      ((h.pow 9).div_const 9)).const_mul 2) using 1
  simp only [id_eq, Nat.cast_ofNat]
  ring

noncomputable def lrAtanh5LowerGap (y : ℝ) : ℝ :=
  2 * Real.artanh y - lrAtanh5 y

lemma hasDerivAt_lrAtanh5LowerGap
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt lrAtanh5LowerGap (2 * y ^ 10 / (1 - y ^ 2)) y := by
  have hart := (hasDerivAt_artanh hy).const_mul 2
  have hpoly := hasDerivAt_lrAtanh5 y
  unfold lrAtanh5LowerGap
  convert hart.sub hpoly using 1
  field_simp [show 1 - y ^ 2 ≠ 0 by nlinarith [hy.1, hy.2]]
  ring

/-- The five positive `atanh` terms are a lower bound on the full function. -/
theorem lrAtanh5_le_two_artanh
    {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    lrAtanh5 y ≤ 2 * Real.artanh y := by
  have hmono : MonotoneOn lrAtanh5LowerGap (Icc (0 : ℝ) y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) y)
    · intro x hx
      have hxOpen : x ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hy.2⟩
      exact (hasDerivAt_lrAtanh5LowerGap hxOpen).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxOpen : x ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hx.1], lt_trans hx.2 hy.2⟩
      exact (hasDerivAt_lrAtanh5LowerGap hxOpen).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxOpen : x ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hx.1], lt_trans hx.2 hy.2⟩
      rw [(hasDerivAt_lrAtanh5LowerGap hxOpen).deriv]
      exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx.1.le _))
        (by nlinarith [hxOpen.1, hxOpen.2])
  have h := hmono (show (0 : ℝ) ∈ Icc 0 y from ⟨le_rfl, hy.1⟩)
    (show y ∈ Icc 0 y from ⟨hy.1, le_rfl⟩) hy.1
  simpa [lrAtanh5LowerGap, lrAtanh5] using h

lemma hasDerivAt_lrAtanh5Upper
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt lrAtanh5Upper
      (2 * (1 + y ^ 2 + y ^ 4 + y ^ 6 + y ^ 8) +
        2 * y ^ 10 * (11 - 9 * y ^ 2) /
          (11 * (1 - y ^ 2) ^ 2)) y := by
  have h := hasDerivAt_id y
  have hnum := (h.pow 11).const_mul 2
  have hden := ((hasDerivAt_const y 1).sub (h.pow 2)).const_mul 11
  have hdenNe : 11 * (1 - y ^ 2) ≠ 0 := by
    have : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
    exact mul_ne_zero (by norm_num) this
  have htail := hnum.div hden hdenNe
  unfold lrAtanh5Upper
  convert (hasDerivAt_lrAtanh5 y).add htail using 1
  simp [id_eq]
  field_simp [hdenNe, show 1 - y ^ 2 ≠ 0 by nlinarith [hy.1, hy.2]]
  ring

noncomputable def lrAtanh5UpperGap (y : ℝ) : ℝ :=
  lrAtanh5Upper y - 2 * Real.artanh y

lemma hasDerivAt_lrAtanh5UpperGap
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt lrAtanh5UpperGap
      (4 * y ^ 12 / (11 * (1 - y ^ 2) ^ 2)) y := by
  have hupper := hasDerivAt_lrAtanh5Upper hy
  have hart := (hasDerivAt_artanh hy).const_mul 2
  unfold lrAtanh5UpperGap
  convert hupper.sub hart using 1
  field_simp [show 1 - y ^ 2 ≠ 0 by nlinarith [hy.1, hy.2]]
  ring

/-- The geometric majorant for the omitted `atanh` tail. -/
theorem two_artanh_le_lrAtanh5Upper
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 3)) :
    2 * Real.artanh y ≤ lrAtanh5Upper y := by
  have hmono : MonotoneOn lrAtanh5UpperGap (Icc (0 : ℝ) (1 / 3)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (1 / 3))
    · intro x hx
      have hxOpen : x ∈ Ioo (-1 : ℝ) 1 := by
        constructor <;> linarith [hx.1, hx.2]
      exact (hasDerivAt_lrAtanh5UpperGap hxOpen).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxOpen : x ∈ Ioo (-1 : ℝ) 1 := by
        constructor <;> linarith [hx.1, hx.2]
      exact (hasDerivAt_lrAtanh5UpperGap hxOpen).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxOpen : x ∈ Ioo (-1 : ℝ) 1 := by
        constructor <;> linarith [hx.1, hx.2]
      rw [(hasDerivAt_lrAtanh5UpperGap hxOpen).deriv]
      positivity
  have h := hmono (show (0 : ℝ) ∈ Icc 0 (1 / 3) by norm_num) hy hy.1
  simpa [lrAtanh5UpperGap, lrAtanh5Upper, lrAtanh5] using h

lemma lrBetaRatio_mem_Icc
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    v / (2 + v) ∈ Icc (0 : ℝ) (1 / 3) := by
  have hden : 0 < 2 + v := by linarith [hv.1]
  constructor
  · exact div_nonneg hv.1 hden.le
  · rw [div_le_iff₀ hden]
    nlinarith [hv.2]

lemma two_artanh_lrBetaRatio
    {v : ℝ} (hv : 0 < v) :
    2 * Real.artanh (v / (2 + v)) = Real.log (1 + v) := by
  have hden : 0 < 2 + v := by linarith
  have hy : v / (2 + v) ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have : 0 < v / (2 + v) := div_pos hv hden
      linarith
    · rw [div_le_one hden]
      linarith
  rw [Real.artanh_eq_half_log hy]
  have hratio :
      (1 + v / (2 + v)) / (1 - v / (2 + v)) = 1 + v := by
    field_simp [hden.ne']
    ring
  rw [hratio]
  ring

theorem lrAtanh5_beta_bounds
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrAtanh5 (v / (2 + v)) ≤ Real.log (1 + v) ∧
      Real.log (1 + v) ≤ lrAtanh5Upper (v / (2 + v)) := by
  have hy := lrBetaRatio_mem_Icc
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2⟩)
  have hlower := lrAtanh5_le_two_artanh
    (show v / (2 + v) ∈ Ico (0 : ℝ) 1 from
      ⟨(div_pos hv.1 (by linarith [hv.1])).le, hy.2.trans_lt (by norm_num)⟩)
  have hupper := two_artanh_le_lrAtanh5Upper hy
  rw [two_artanh_lrBetaRatio hv.1] at hlower hupper
  exact ⟨hlower, hupper⟩

theorem lrAtanh5_log_lower
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrAtanh5 ((1 - v) / (1 + v)) ≤ -Real.log v := by
  by_cases hv1 : v = 1
  · subst v
    norm_num [lrAtanh5]
  have homega : (1 - v) / (1 + v) ∈ Ico (0 : ℝ) 1 := by
    have hplus : 0 < 1 + v := by linarith [hv.1]
    constructor
    · exact div_nonneg (sub_nonneg.mpr hv.2) hplus.le
    · rw [div_lt_one hplus]
      linarith [hv.1]
  have h := lrAtanh5_le_two_artanh homega
  have hlog := two_mul_artanh_lrScalarLogRatio
    (show v ∈ Ioo (0 : ℝ) 1 from ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩)
  unfold lrScalarLogRatio at hlog
  rw [hlog] at h
  exact h

end CourtadeKumar
