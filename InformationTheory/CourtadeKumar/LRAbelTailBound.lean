import InformationTheory.CourtadeKumar.LRAbelTailIntegral

/-! The audited three-term upper bound for the Abel logarithmic tail. -/

open Set
open scoped Interval

namespace CourtadeKumar

noncomputable def lrAbelTailMajorant (N : ℕ) (y : ℝ) : ℝ :=
  y ^ (2 * N) / 2 +
    y ^ (2 * N) * (1 - y) / 4 +
    y ^ (2 * N) * (1 - y) ^ 2 / 4

lemma lrAbelTailIntegrand_le_majorant
    (N : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    y ^ (2 * N) / (1 + y) ≤ lrAbelTailMajorant N y := by
  have hden : 0 < 1 + y := by nlinarith [hy.1]
  have hrecip := lr_reciprocal_tail_decomposition (by linarith : y ≠ -1)
  have hlast :
      (1 - y) ^ 2 / (4 * (1 + y)) ≤ (1 - y) ^ 2 / 4 := by
    have hsq : 0 ≤ (1 - y) ^ 2 := sq_nonneg (1 - y)
    rw [div_le_iff₀ (by positivity : 0 < 4 * (1 + y))]
    calc
      (1 - y) ^ 2 ≤ (1 - y) ^ 2 * (1 + y) := by
        nlinarith [mul_nonneg hsq hy.1]
      _ = (1 - y) ^ 2 / 4 * (4 * (1 + y)) := by ring
  have hpow : 0 ≤ y ^ (2 * N) := pow_nonneg hy.1 _
  calc
    y ^ (2 * N) / (1 + y) = y ^ (2 * N) * (1 / (1 + y)) := by ring
    _ = y ^ (2 * N) *
        (1 / 2 + (1 - y) / 4 + (1 - y) ^ 2 / (4 * (1 + y))) := by rw [hrecip]
    _ ≤ y ^ (2 * N) *
        (1 / 2 + (1 - y) / 4 + (1 - y) ^ 2 / 4) := by
      apply mul_le_mul_of_nonneg_left _ hpow
      linarith
    _ = lrAbelTailMajorant N y := by
      unfold lrAbelTailMajorant
      ring

lemma lrAbelTailMajorant_intervalIntegrable (N : ℕ) :
    IntervalIntegrable (lrAbelTailMajorant N)
      MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold lrAbelTailMajorant
  fun_prop

lemma lrAbelTailMajorant_eq_polynomial (N : ℕ) (y : ℝ) :
    lrAbelTailMajorant N y =
      y ^ (2 * N) - (3 / 4 : ℝ) * y ^ (2 * N + 1) +
        (1 / 4 : ℝ) * y ^ (2 * N + 2) := by
  have hpow1 : y ^ (2 * N + 1) = y ^ (2 * N) * y := by rw [pow_succ]
  have hpow2 : y ^ (2 * N + 2) = y ^ (2 * N) * y ^ 2 := by rw [pow_add]
  unfold lrAbelTailMajorant
  rw [hpow1, hpow2]
  ring

theorem lrAbelTailIntegral_le_majorant_integral (N : ℕ) :
    lrAbelTailIntegral N ≤
      ∫ y : ℝ in 0..1, lrAbelTailMajorant N y := by
  unfold lrAbelTailIntegral
  exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num)
    (lrAbelTailIntegrand_intervalIntegrable N)
    (lrAbelTailMajorant_intervalIntegrable N)
    (fun y hy ↦ lrAbelTailIntegrand_le_majorant N hy)

theorem lrAbelTailMajorant_integral (N : ℕ) :
    (∫ y : ℝ in 0..1, lrAbelTailMajorant N y) =
      1 / (2 * (2 * (N : ℝ) + 1)) +
        1 / (4 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) +
        1 / (2 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2) *
          (2 * (N : ℝ) + 3)) := by
  have hpow0 : IntervalIntegrable (fun y : ℝ ↦ y ^ (2 * N))
      MeasureTheory.volume 0 1 :=
    (continuous_pow (2 * N)).intervalIntegrable 0 1
  have hpow1 : IntervalIntegrable
      (fun y : ℝ ↦ (3 / 4 : ℝ) * y ^ (2 * N + 1))
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_pow (2 * N + 1))).intervalIntegrable 0 1
  have hpow2 : IntervalIntegrable
      (fun y : ℝ ↦ (1 / 4 : ℝ) * y ^ (2 * N + 2))
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_pow (2 * N + 2))).intervalIntegrable 0 1
  have hcongr :
      (∫ y : ℝ in 0..1, lrAbelTailMajorant N y) =
        ∫ y : ℝ in 0..1,
          (y ^ (2 * N) - (3 / 4 : ℝ) * y ^ (2 * N + 1)) +
            (1 / 4 : ℝ) * y ^ (2 * N + 2) := by
    apply intervalIntegral.integral_congr
    intro y _
    exact lrAbelTailMajorant_eq_polynomial N y
  rw [hcongr]
  rw [intervalIntegral.integral_add (hpow0.sub hpow1) hpow2]
  rw [intervalIntegral.integral_sub hpow0 hpow1]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_pow, integral_pow, integral_pow]
  norm_num only [one_pow, zero_pow, Nat.succ_ne_zero, sub_zero]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

theorem lrAbelTailValue_bound
    {N : ℕ} (hN : 1 ≤ N) :
    lrAbelTailValue N ≤
      (4 * (N : ℝ) + 1) /
        (8 * (N : ℝ) * (2 * (N : ℝ) + 1)) := by
  rw [lrAbelTailValue_eq_integral]
  calc
    lrAbelTailIntegral N ≤
        ∫ y : ℝ in 0..1, lrAbelTailMajorant N y :=
      lrAbelTailIntegral_le_majorant_integral N
    _ = 1 / (2 * (2 * (N : ℝ) + 1)) +
        1 / (4 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) +
        1 / (2 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2) *
          (2 * (N : ℝ) + 3)) := lrAbelTailMajorant_integral N
    _ ≤ _ := lr_abel_tail_rational_bound hN

theorem lrAbelPrefixS_quantitative_lower
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    v ^ (2 * N + 1) / (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) ≤
      lrAbelPrefixS N v :=
  lrAbelPrefixS_lower_of_tail hN (lrAbelTailValue_bound (by omega)) hv

end CourtadeKumar
