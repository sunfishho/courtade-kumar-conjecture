import InformationTheory.CourtadeKumar.LRLowShapeUSecondScalarBridge

/-! The twelve-term rational lower envelope for `G_t(v)` used in the
finite heads of the second low-shape `U` scalar. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowPhiFirst12 (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 12, lrLowA (k + 1) * x ^ (k + 1)

noncomputable def lrLowPhiSecond12 (v x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 12,
    lrLowA (k + 1) * x ^ (k + 1) * v ^ (2 * (k + 1) - 1)

noncomputable def lrLowPhi12Upper (v x : ℝ) : ℝ :=
  lrLowPhiFirst12 x + lrLowPhiSecond12 v x +
    lrLowA 13 * x ^ 13 / (1 - x) +
    lrLowA 13 * x ^ 13 * v ^ 25 / (1 - v ^ 2 * x)

noncomputable def lrLowGShapeLower (v x : ℝ) : ℝ :=
  lrLowGLower v - lrLowPhi12Upper v x

lemma lrLowPhiPrefix_twelve_eq
    (v x : ℝ) :
    lrLowPhiPrefix v x 12 =
      lrLowPhiFirst12 x + lrLowPhiSecond12 v x := by
  unfold lrLowPhiPrefix lrLowPhiFirst12 lrLowPhiSecond12 lrLowT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lrLow_topPhi_first_upper
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    topPhi t ≤ lrLowPhiFirst12 (t ^ 2) +
      lrLowA 13 * (t ^ 2) ^ 13 / (1 - t ^ 2) := by
  have hsqrt : Real.sqrt (t ^ 2) = t := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
  have htail := topPhi_sqrt_tail_twelve_upper
    (sq_pos_of_pos ht.1) (by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)])
  rw [hsqrt] at htail
  have hupper : topPhi t ≤
      (∑ n ∈ Finset.range 12,
        (t ^ 2) ^ (n + 1) /
          (2 * (n + 1) * (2 * (n + 1) - 1))) +
        (1 / (2 * 13 * (2 * 13 - 1)) : ℝ) *
          (t ^ 2) ^ 13 / (1 - t ^ 2) := by
    linarith
  calc
    topPhi t ≤
        (∑ n ∈ Finset.range 12,
          (t ^ 2) ^ (n + 1) /
            (2 * (n + 1) * (2 * (n + 1) - 1))) +
          (1 / (2 * 13 * (2 * 13 - 1)) : ℝ) *
            (t ^ 2) ^ 13 / (1 - t ^ 2) := hupper
    _ = lrLowPhiFirst12 (t ^ 2) +
        lrLowA 13 * (t ^ 2) ^ 13 / (1 - t ^ 2) := by
      congr 1
      · unfold lrLowPhiFirst12
        apply Finset.sum_congr rfl
        intro k hk
        unfold lrLowA
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring

lemma lrLow_topPhi_second_upper
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    topPhi (v * t) / v ≤ lrLowPhiSecond12 v (t ^ 2) +
      lrLowA 13 * (t ^ 2) ^ 13 * v ^ 25 /
        (1 - v ^ 2 * t ^ 2) := by
  have hq0 : 0 < v ^ 2 * t ^ 2 :=
    mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hvt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have hq1 : v ^ 2 * t ^ 2 < 1 := by
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  have hsqrt := lrLow_sqrt_sq_product hv.1.le ht.1.le
  have htail := topPhi_sqrt_tail_twelve_upper hq0 hq1
  rw [hsqrt] at htail
  have hdiv := div_le_div_of_nonneg_right htail hv.1.le
  have hupper : topPhi (v * t) / v ≤
      (∑ n ∈ Finset.range 12,
        (v ^ 2 * t ^ 2) ^ (n + 1) /
          (2 * (n + 1) * (2 * (n + 1) - 1))) / v +
        ((1 / (2 * 13 * (2 * 13 - 1)) : ℝ) *
          (v ^ 2 * t ^ 2) ^ 13 / (1 - v ^ 2 * t ^ 2)) / v := by
    calc
      topPhi (v * t) / v =
          (topPhi (v * t) -
            ∑ n ∈ Finset.range 12,
              (v ^ 2 * t ^ 2) ^ (n + 1) /
                (2 * (n + 1) * (2 * (n + 1) - 1))) / v +
            (∑ n ∈ Finset.range 12,
              (v ^ 2 * t ^ 2) ^ (n + 1) /
                (2 * (n + 1) * (2 * (n + 1) - 1))) / v := by ring
      _ ≤ (1 / (2 * 13 * (2 * 13 - 1)) : ℝ) *
            (v ^ 2 * t ^ 2) ^ 13 / (1 - v ^ 2 * t ^ 2) / v +
          (∑ n ∈ Finset.range 12,
            (v ^ 2 * t ^ 2) ^ (n + 1) /
              (2 * (n + 1) * (2 * (n + 1) - 1))) / v :=
        by
          convert add_le_add_right hdiv
            ((∑ n ∈ Finset.range 12,
              (v ^ 2 * t ^ 2) ^ (n + 1) /
                (2 * (n + 1) * (2 * (n + 1) - 1))) / v) using 1 <;>
            ring
      _ = (∑ n ∈ Finset.range 12,
            (v ^ 2 * t ^ 2) ^ (n + 1) /
              (2 * (n + 1) * (2 * (n + 1) - 1))) / v +
          ((1 / (2 * 13 * (2 * 13 - 1)) : ℝ) *
            (v ^ 2 * t ^ 2) ^ 13 / (1 - v ^ 2 * t ^ 2)) / v := by ring
  calc
    topPhi (v * t) / v ≤ _ := hupper
    _ = lrLowPhiSecond12 v (t ^ 2) +
        lrLowA 13 * (t ^ 2) ^ 13 * v ^ 25 /
          (1 - v ^ 2 * t ^ 2) := by
      congr 1
      · unfold lrLowPhiSecond12
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        unfold lrLowA
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [mul_pow, ← pow_mul]
        field_simp [hv.1.ne']
        rw [show 2 * (k + 1) = (2 * (k + 1) - 1) + 1 by omega,
          pow_succ]
        rw [show 2 * (k + 1) - 1 + 1 - 1 = 2 * (k + 1) - 1 by omega]
        ring
      · unfold lrLowA
        field_simp [hv.1.ne']
        ring

theorem lrLowGShapeLower_le
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowGShapeLower v (t ^ 2) ≤ lrGShape t v := by
  have hfirst := lrLow_topPhi_first_upper ht
  have hsecond := lrLow_topPhi_second_upper hv ht
  have hg := lrLowGLower_le_lrG
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  unfold lrLowGShapeLower lrLowPhi12Upper lrGShape
  linarith

end CourtadeKumar
