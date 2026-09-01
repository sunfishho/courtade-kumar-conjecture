import InformationTheory.CourtadeKumar.LRLowShapeTailData
import InformationTheory.CourtadeKumar.LRWSeries

/-! Lightweight exact resummation of the weighted endpoint tails. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

lemma lrLowB_le_log_two (n : ℕ) :
    lrLowB n ≤ Real.log 2 := by
  unfold lrLowB
  exact sub_le_self _ (Finset.sum_nonneg fun k hk ↦
    (lrLowA_pos (by omega)).le)

lemma lrLowA_mul_pred_eq_lrAbelA (j : ℕ) :
    ((j : ℝ) - 1) * lrLowA j = lrAbelA j := by
  unfold lrLowA lrAbelA
  ring

lemma lrLowA_succ_mul_eq_lrAbelB (j : ℕ) :
    ((j : ℝ) + 1) * lrLowA (j + 1) = lrAbelB j := by
  unfold lrLowA lrAbelB
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hplus : 2 * (j : ℝ) + 1 ≠ 0 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  rw [show 2 * ((j : ℝ) + 1) - 1 = 2 * (j : ℝ) + 1 by ring]
  field_simp [hj1, hplus]

lemma lrWOmega_one_eq_tail_second_difference (j : ℕ) :
    lrWOmega j 1 =
      ((j : ℝ) - 1) * lrLowA j - (j + 1) * lrLowA (j + 1) := by
  unfold lrWOmega
  simp only [one_pow, mul_one]
  rw [lrLowA_mul_pred_eq_lrAbelA, lrLowA_succ_mul_eq_lrAbelB]

lemma lrLowB_weighted_second_difference (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) * lrLowB (j + 1) -
          2 * (j : ℝ) * lrLowB j +
          ((j : ℝ) - 1) * lrLowB (j - 1) =
      ((j : ℝ) - 1) * lrLowA j -
        ((j : ℝ) + 1) * lrLowA (j + 1) := by
  by_cases hj : j = 0
  · subst j
    have h := lrLowB_recursion 0
    norm_num [lrLowA] at h ⊢
    linarith
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hprev := lrLowB_recursion (j - 1)
    have hnext := lrLowB_recursion j
    rw [show j - 1 + 1 = j by omega] at hprev
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

lemma summable_lrLowB_derivative
    {R : ℝ} (hR : R ∈ Ico (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) * lrLowB (n + 1) * R ^ n) := by
  have hnorm : ‖R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hR.1]
    exact hR.2
  have hweighted : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * R ^ n) := by
    have hn := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hg := (summable_geometric_of_norm_lt_one hnorm)
    convert hn.add hg using 1
    funext n
    ring
  have hbound := hweighted.mul_left (Real.log 2)
  apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg
        (mul_nonneg (by positivity) (lrLowB_pos (n + 1)).le)
        (pow_nonneg hR.1 n)) _ hbound
  intro n
  have hb := lrLowB_le_log_two (n + 1)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hn : 0 ≤ ((n : ℝ) + 1) := by positivity
  have hpow : 0 ≤ R ^ n := pow_nonneg hR.1 n
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    ((n : ℝ) + 1) * lrLowB (n + 1) * R ^ n ≤
        ((n : ℝ) + 1) * Real.log 2 * R ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb hn) hpow
    _ = Real.log 2 * (((n : ℝ) + 1) * R ^ n) := by ring

theorem lrLowB_derivative_hasSum
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) * lrLowB (n + 1) * R ^ n)
      (lrWKernel R 1 / (1 - R) ^ 2) := by
  let f : ℕ → ℝ := fun n ↦
    ((n + 1 : ℕ) : ℝ) * lrLowB (n + 1) * R ^ n
  let D : ℝ := ∑' n : ℕ, f n
  have hf : HasSum f D :=
    (summable_lrLowB_derivative
      (show R ∈ Ico (0 : ℝ) 1 from ⟨hR.1.le, hR.2⟩)).hasSum
  let f1 : ℕ → ℝ
    | 0 => 0
    | n + 1 => R * f n
  let f2 : ℕ → ℝ
    | 0 => 0
    | n + 1 => R * f1 n
  have hf1 : HasSum f1 (R * D) := by
    simpa [f1] using lr_hasSum_power_shift f R D hf
  have hf2 : HasSum f2 (R * (R * D)) := by
    simpa [f2] using lr_hasSum_power_shift f1 R (R * D) hf1
  have hcomb := (hf.sub (hf1.mul_left 2)).add hf2
  let g : ℕ → ℝ
    | 0 => lrLowB 1
    | n + 1 => lrWOmega (n + 1) 1 * R ^ (n + 1)
  have hfg : ∀ n : ℕ, f n - 2 * f1 n + f2 n = g n := by
    intro n
    rcases n with _ | n
    · simp [f, f1, f2, g]
    rcases n with _ | n
    · have hdiff := lrLowB_weighted_second_difference 1
      simp only [f, f1, f2, g]
      rw [lrWOmega_one_eq_tail_second_difference]
      norm_num only [Nat.cast_add, Nat.cast_one] at hdiff ⊢
      linear_combination R * hdiff
    · have hdiff := lrLowB_weighted_second_difference (n + 2)
      simp only [f, f1, f2, g]
      rw [lrWOmega_one_eq_tail_second_difference]
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ R (n + 1), pow_succ R n]
      rw [show n + 2 - 1 = n + 1 by omega] at hdiff
      norm_num only [Nat.cast_add, Nat.cast_one] at hdiff
      linear_combination R ^ (n + 2) * hdiff
  have hg : HasSum g (D * (1 - R) ^ 2) := by
    convert hcomb using 1
    · funext n
      exact (hfg n).symm
    · ring
  have htail := (summable_lrWExtended_tail
    (show R ∈ Ico (0 : ℝ) 1 from ⟨hR.1.le, hR.2⟩)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)).hasSum
  have hgW : HasSum g (lrWExtended R 1) := by
    have hshift : HasSum (fun n : ℕ ↦ g (n + 1))
        (∑' n : ℕ, lrWOmega (n + 1) 1 * R ^ (n + 1)) := by
      simpa [g] using htail
    have hfull := (hasSum_nat_add_iff (f := g) 1).mp hshift
    have hval :
        (∑' n : ℕ, lrWOmega (n + 1) 1 * R ^ (n + 1)) +
            ∑ i ∈ Finset.range 1, g i = lrWExtended R 1 := by
      simp [g, lrWExtended, lrWZero, lrLowB, lrLowA]
      ring
    rw [hval] at hfull
    exact hfull
  have hvalue : D * (1 - R) ^ 2 = lrWKernel R 1 := by
    rw [← lrWExtended_eq_lrWKernel hR (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)]
    exact hg.unique hgW
  have hden : (1 - R) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
  have hD : D = lrWKernel R 1 / (1 - R) ^ 2 := by
    rw [eq_div_iff hden]
    exact hvalue
  simpa [f, hD] using hf

end CourtadeKumar
