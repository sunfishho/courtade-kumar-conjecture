import InformationTheory.CourtadeKumar.LRLowShapeUTailSeries

/-! Exact resummation of the weighted shape tails used in the
low-shape `U` certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

lemma lrWOmega_pair_eq_weighted_tail_difference
    {v t : ℝ} (hv : 0 < v) {j : ℕ} (hj : 1 ≤ j) :
    lrWOmega j t + lrWOmega j (v * t) / v =
      ((j : ℝ) - 1) * lrLowA j * lrLowT v (t ^ 2) j -
        ((j : ℝ) + 1) * lrLowA (j + 1) *
          lrLowT v (t ^ 2) (j + 1) := by
  have heven : 2 * j = (2 * j - 1) + 1 := by omega
  have hnext : 2 * j + 2 = (2 * j + 1) + 1 := by omega
  have htj : (t ^ 2) ^ j = t ^ (2 * j) := by rw [pow_mul]
  have htj1 : (t ^ 2) ^ (j + 1) = t ^ (2 * j + 2) := by
    rw [pow_succ, htj, ← pow_add]
  unfold lrWOmega lrLowT
  rw [← lrLowA_mul_pred_eq_lrAbelA,
    ← lrLowA_succ_mul_eq_lrAbelB, htj, htj1]
  rw [mul_pow, mul_pow]
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  rw [show v ^ (2 * j) = v ^ (2 * j - 1) * v by
        calc
          v ^ (2 * j) = v ^ ((2 * j - 1) + 1) := congrArg (v ^ ·) heven
          _ = v ^ (2 * j - 1) * v := pow_succ _ _,
    show v ^ (2 * j + 2) = v ^ (2 * j + 1) * v by
        calc
          v ^ (2 * j + 2) = v ^ ((2 * j + 1) + 1) := congrArg (v ^ ·) hnext
          _ = v ^ (2 * j + 1) * v := pow_succ _ _]
  field_simp [hv.ne']
  ring

lemma lrLowP_weighted_second_difference
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) * lrLowP v x (j + 1) -
          2 * (j : ℝ) * lrLowP v x j +
          ((j : ℝ) - 1) * lrLowP v x (j - 1) =
      ((j : ℝ) - 1) * lrLowA j * lrLowT v x j -
        ((j : ℝ) + 1) * lrLowA (j + 1) * lrLowT v x (j + 1) := by
  by_cases hj : j = 0
  · subst j
    have h := lrLowP_recursion hv hx 0
    norm_num [lrLowA] at h ⊢
    linarith
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hprev := lrLowP_recursion hv hx (j - 1)
    have hnext := lrLowP_recursion hv hx j
    rw [show j - 1 + 1 = j by omega] at hprev
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

lemma summable_lrLowP_derivative
    {R v x : ℝ} (hR : R ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) * lrLowP v x (n + 1) * R ^ n) := by
  have hb := summable_lrLowB_derivative hR |>.mul_left 2
  apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg
        (mul_nonneg (by positivity) (by
          rw [← (lrLowP_hasSum hv hx (n + 1)).tsum_eq]
          exact tsum_nonneg fun k ↦ mul_nonneg
            (lrLowA_pos (by omega)).le (lrLowT_nonneg hv.1 hx.1 _)))
        (pow_nonneg hR.1 n)) _ hb
  intro n
  have hp := lrLowP_le_first_mul_B hv hx (n + 1)
  have hT := lrLowT_le_two hv hx (n + 2)
  have hb0 := (lrLowB_pos (n + 1)).le
  have hpBound : lrLowP v x (n + 1) ≤ 2 * lrLowB (n + 1) :=
    hp.trans (mul_le_mul_of_nonneg_right hT hb0)
  have hn : 0 ≤ ((n : ℝ) + 1) := by positivity
  have hpow : 0 ≤ R ^ n := pow_nonneg hR.1 n
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    ((n : ℝ) + 1) * lrLowP v x (n + 1) * R ^ n ≤
        ((n : ℝ) + 1) * (2 * lrLowB (n + 1)) * R ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpBound hn) hpow
    _ = 2 * ((n : ℝ) + 1) * lrLowB (n + 1) * R ^ n := by ring
    _ = 2 * (((n : ℝ) + 1) * lrLowB (n + 1) * R ^ n) := by ring

theorem lrLowP_derivative_hasSum
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) * lrLowP v (t ^ 2) (n + 1) * R ^ n)
      (lrFlowPW R v t / (1 - R) ^ 2) := by
  let f : ℕ → ℝ := fun n ↦
    ((n + 1 : ℕ) : ℝ) * lrLowP v (t ^ 2) (n + 1) * R ^ n
  let D : ℝ := ∑' n : ℕ, f n
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have htClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have hf : HasSum f D :=
    (summable_lrLowP_derivative
      (show R ∈ Ico (0 : ℝ) 1 from ⟨hR.1.le, hR.2⟩)
      hvClosed htClosed).hasSum
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
    | 0 => lrLowP v (t ^ 2) 1
    | n + 1 =>
        (lrWOmega (n + 1) t + lrWOmega (n + 1) (v * t) / v) *
          R ^ (n + 1)
  have hfg : ∀ n : ℕ, f n - 2 * f1 n + f2 n = g n := by
    intro n
    rcases n with _ | n
    · simp [f, f1, f2, g]
    rcases n with _ | n
    · have hdiff := lrLowP_weighted_second_difference hvClosed htClosed 1
      simp only [f, f1, f2, g]
      rw [lrWOmega_pair_eq_weighted_tail_difference hv.1 (j := 1) (by omega)]
      norm_num only [Nat.cast_add, Nat.cast_one] at hdiff ⊢
      linear_combination R * hdiff
    · have hdiff := lrLowP_weighted_second_difference hvClosed htClosed (n + 2)
      simp only [f, f1, f2, g]
      rw [lrWOmega_pair_eq_weighted_tail_difference hv.1
        (j := n + 2) (by omega)]
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
  have htailT := (summable_lrWExtended_tail
    (show R ∈ Ico (0 : ℝ) 1 from ⟨hR.1.le, hR.2⟩)
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)).hasSum
  have hvt : v * t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg hv.1.le ht.1.le
    · exact (calc
        v * t ≤ 1 * t := mul_le_mul_of_nonneg_right hv.2.le ht.1.le
        _ < 1 := by simpa using ht.2).le
  have htailVT := (summable_lrWExtended_tail
    (show R ∈ Ico (0 : ℝ) 1 from ⟨hR.1.le, hR.2⟩) hvt).hasSum
  have htail : HasSum (fun n : ℕ ↦
      (lrWOmega (n + 1) t + lrWOmega (n + 1) (v * t) / v) * R ^ (n + 1))
      ((∑' n : ℕ, lrWOmega (n + 1) t * R ^ (n + 1)) +
        (∑' n : ℕ, lrWOmega (n + 1) (v * t) * R ^ (n + 1)) / v) := by
    convert htailT.add (htailVT.mul_left (1 / v)) using 1
    · funext n
      ring
    · ring
  have hgW : HasSum g
      (lrWExtended R t + lrWExtended R (v * t) / v) := by
    have hshift : HasSum (fun n : ℕ ↦ g (n + 1))
        ((∑' n : ℕ, lrWOmega (n + 1) t * R ^ (n + 1)) +
          (∑' n : ℕ, lrWOmega (n + 1) (v * t) * R ^ (n + 1)) / v) := by
      simpa [g] using htail
    have hfull := (hasSum_nat_add_iff (f := g) 1).mp hshift
    have hbase : lrLowP v (t ^ 2) 1 =
        lrWZero t + lrWZero (v * t) / v := by
      have hzero := lrLowP_zero_eq_phi hv
        (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
      have hrec := lrLowP_recursion hvClosed htClosed 0
      rw [hzero] at hrec
      unfold lrWZero
      norm_num [lrLowA, lrLowT] at hrec ⊢
      field_simp [hv.1.ne'] at hrec ⊢
      nlinarith
    have hval :
        ((∑' n : ℕ, lrWOmega (n + 1) t * R ^ (n + 1)) +
          (∑' n : ℕ, lrWOmega (n + 1) (v * t) * R ^ (n + 1)) / v) +
            ∑ i ∈ Finset.range 1, g i =
          lrWExtended R t + lrWExtended R (v * t) / v := by
      simp [g, lrWExtended, hbase]
      ring
    rw [hval] at hfull
    exact hfull
  have hvalue : D * (1 - R) ^ 2 = lrFlowPW R v t := by
    unfold lrFlowPW
    rw [← lrWExtended_eq_lrWKernel hR
      (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      ← lrWExtended_eq_lrWKernel hR
        (show v * t ∈ Ioc (0 : ℝ) 1 from
          ⟨mul_pos hv.1 ht.1, hvt.2⟩)]
    exact hg.unique hgW
  have hden : (1 - R) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')
  have hD : D = lrFlowPW R v t / (1 - R) ^ 2 := by
    rw [eq_div_iff hden]
    exact hvalue
  simpa [f, hD] using hf

end CourtadeKumar
