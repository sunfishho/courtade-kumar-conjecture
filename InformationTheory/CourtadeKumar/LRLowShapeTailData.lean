import InformationTheory.CourtadeKumar.LRLowShapeUReduction

/-! Exact endpoint tails and the bounds on `Kₙ` used in the low-shape
midpoint certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowA (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) * (2 * (n : ℝ) - 1))

noncomputable def lrLowB (j : ℕ) : ℝ :=
  Real.log 2 - ∑ k ∈ Finset.range j, lrLowA (k + 1)

lemma lrLowA_eq_phi_coefficient (n : ℕ) :
    lrLowA (n + 1) =
      (1 : ℝ) / (2 * (n + 1) * (2 * (n + 1) - 1)) := by
  unfold lrLowA
  norm_num only [Nat.cast_add, Nat.cast_one]

theorem lrLowB_hasSum (j : ℕ) :
    HasSum (fun k : ℕ ↦ lrLowA (k + j + 1)) (lrLowB j) := by
  convert top_hasSum_phiCoefficients_tail j using 1
  · funext k
    unfold lrLowA
    norm_num only [Nat.cast_add, Nat.cast_one]
  · unfold lrLowB
    apply congrArg (fun z : ℝ ↦ Real.log 2 - z)
    apply Finset.sum_congr rfl
    intro k hk
    exact lrLowA_eq_phi_coefficient k

lemma lrLowA_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < lrLowA n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lrLowA
  have hfirst : (0 : ℝ) < 2 * n := by positivity
  have hsecond : (0 : ℝ) < 2 * (n : ℝ) - 1 := by nlinarith
  exact one_div_pos.mpr (mul_pos hfirst hsecond)

lemma lrLowB_first_term_le (j : ℕ) :
    lrLowA (j + 1) ≤ lrLowB j := by
  have hsum := lrLowB_hasSum j
  rw [← hsum.tsum_eq]
  have hnonneg : ∀ k : ℕ, 0 ≤ lrLowA (k + j + 1) := by
    intro k
    exact (lrLowA_pos (by omega)).le
  have h := hsum.summable.sum_le_tsum ({0} : Finset ℕ)
    (fun k _ ↦ hnonneg k)
  simpa using h

lemma lrLowB_pos (j : ℕ) : 0 < lrLowB j :=
  (lrLowA_pos (by omega : 1 ≤ j + 1)).trans_le (lrLowB_first_term_le j)

lemma lrLowB_recursion (j : ℕ) :
    lrLowB j = lrLowA (j + 1) + lrLowB (j + 1) := by
  unfold lrLowB
  rw [Finset.sum_range_succ]
  ring

noncomputable def lrLowC (j : ℕ) : ℝ :=
  1 / (2 * (2 * (j : ℝ) + 1))

lemma lrLowC_nonneg (j : ℕ) : 0 ≤ lrLowC j := by
  unfold lrLowC
  positivity

lemma lrLowC_tendsto_zero :
    Filter.Tendsto lrLowC Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun n ↦ lrLowC_nonneg n)
    (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  unfold lrLowC
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsmall : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlarge : (0 : ℝ) < 2 * (2 * (n : ℝ) + 1) := by positivity
  rw [div_le_div_iff₀ hlarge hsmall]
  nlinarith

lemma lrLowC_diff_nonneg (j : ℕ) :
    0 ≤ lrLowC j - lrLowC (j + 1) := by
  unfold lrLowC
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hden0 : (0 : ℝ) < 2 * (2 * (j : ℝ) + 1) := by positivity
  have hden1 : (0 : ℝ) < 2 * (2 * ((j : ℝ) + 1) + 1) := by positivity
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [sub_nonneg, div_le_div_iff₀ hden1 hden0]
  nlinarith

lemma lrLowC_diff_hasSum (j : ℕ) :
    HasSum (fun k : ℕ ↦ lrLowC (k + j) - lrLowC (k + j + 1))
      (lrLowC j) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k ↦ by simpa [add_assoc] using lrLowC_diff_nonneg (k + j))]
  have hshift : Filter.Tendsto (fun n : ℕ ↦ lrLowC (n + j))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat j).2 lrLowC_tendsto_zero
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ lrLowC j)
      Filter.atTop (nhds (lrLowC j)) := tendsto_const_nhds
  have hlim := hconst.sub hshift
  have hsum (n : ℕ) :
      ∑ i ∈ Finset.range n,
          (lrLowC (i + j) - lrLowC (i + j + 1)) =
        lrLowC j - lrLowC (n + j) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      Finset.sum_range_sub' (fun i ↦ lrLowC (i + j)) n
  convert hlim using 1
  · funext n
    exact hsum n
  · simp

private lemma lrLowC_diff_le_A
    {m : ℕ} (hm : 1 ≤ m) :
    lrLowC (m - 1) - lrLowC m ≤ lrLowA m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℝ) < 2 * (m : ℝ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have h3 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hcPrev : lrLowC (m - 1) =
      1 / (2 * (2 * (m : ℝ) - 1)) := by
    unfold lrLowC
    rw [Nat.cast_sub hm]
    norm_num only [Nat.cast_one]
    congr 2
    ring
  have hcNow : lrLowC m = 1 / (2 * (2 * (m : ℝ) + 1)) := rfl
  have haNow : lrLowA m = 1 / (2 * (m : ℝ) * (2 * (m : ℝ) - 1)) := rfl
  rw [hcPrev, hcNow, haNow]
  field_simp [h1.ne', h2.ne', h3.ne']
  nlinarith

lemma lrLowC_diff_le_A_tail (j k : ℕ) :
    lrLowC (k + j) - lrLowC (k + j + 1) ≤
      lrLowA (k + j + 1) := by
  convert lrLowC_diff_le_A (m := k + j + 1) (by omega) using 1 <;>
    congr 1 <;> omega

lemma lrLowC_le_B (j : ℕ) : lrLowC j ≤ lrLowB j := by
  have hc := lrLowC_diff_hasSum j
  have hb := lrLowB_hasSum j
  rw [← hc.tsum_eq, ← hb.tsum_eq]
  exact hc.summable.tsum_le_tsum (lrLowC_diff_le_A_tail j) hb.summable

/-- The sequence `j b_j` is increasing. -/
theorem lrLowB_scaled_monotone :
    Monotone (fun j : ℕ ↦ (j : ℝ) * lrLowB j) := by
  apply monotone_nat_of_le_succ
  intro j
  have hlower := lrLowC_le_B j
  have hrec := lrLowB_recursion j
  have hidentity : (j + 1 : ℝ) * lrLowA (j + 1) = lrLowC j := by
    unfold lrLowA lrLowC
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hden : 1 + (j : ℝ) * 2 ≠ 0 := by nlinarith
    ring_nf
    field_simp [hden]
    ring
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith [hidentity]

/-- The tail-ratio estimate `b_j/b_n ≤ n/j`. -/
theorem lrLowB_ratio_le
    {j n : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    lrLowB j / lrLowB n ≤ (n : ℝ) / j := by
  have hscaled := lrLowB_scaled_monotone hjn
  have hbn := lrLowB_pos n
  have hjR : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  rw [div_le_div_iff₀ hbn hjR]
  simpa [mul_comm] using hscaled

/-- A reversed finite head of the `L` series.  This indexing matches the
convolution in `Kₙ` and avoids hiding a finite reindexing in later algebra. -/
noncomputable def lrLowLHead (xi : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1),
    xi ^ (n - (k + 1)) / (2 * ((n - (k + 1) : ℕ) : ℝ))

lemma lrLowLHead_eq_prefix (xi : ℝ) (n : ℕ) :
    lrLowLHead xi n =
      ∑ k ∈ Finset.range (n - 1),
        xi ^ (k + 1) / (2 * (k + 1)) := by
  unfold lrLowLHead
  rw [← Finset.sum_range_reflect
    (fun k : ℕ ↦ xi ^ (k + 1) / (2 * (k + 1))) (n - 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt := Finset.mem_range.mp hk
  rw [show n - (k + 1) = (n - 1 - 1 - k) + 1 by omega]
  norm_num only [Nat.cast_add, Nat.cast_one]

lemma lrLowLHead_le_lrL_sqrt
    {xi : ℝ} (hxi : xi ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    lrLowLHead xi n ≤ lrL (Real.sqrt xi) := by
  rw [lrLowLHead_eq_prefix]
  exact lrL_sqrt_partial_sum_le hxi (n - 1)

lemma lrLowH_le_nat
    {xi : ℝ} (hxi : xi ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    lrLowH xi n ≤ n := by
  unfold lrLowH
  calc
    ∑ k ∈ Finset.range n, xi ^ (k + 1) ≤
        ∑ _k ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact pow_le_one₀ hxi.1 hxi.2
    _ = n := by simp

lemma lrLowK_lower
    {beta xi : ℝ} {n : ℕ}
    (hbeta : 0 ≤ beta) (hxi : xi ∈ Icc (0 : ℝ) 1) :
    beta * lrLowH xi n ≤ lrLowK beta xi lrLowB n := by
  have hH := lrLowH_le_nat hxi n
  have hbase : beta * lrLowH xi n ≤ beta * n :=
    mul_le_mul_of_nonneg_left hH hbeta
  have hsum : 0 ≤
      ∑ k ∈ Finset.range (n - 1),
        lrLowEtaWeight xi n k * (lrLowB (k + 1) / lrLowB n) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (lrLowEtaWeight_nonneg hxi.1 hk)
      (div_nonneg (lrLowB_pos _).le (lrLowB_pos _).le)
  unfold lrLowK
  exact hbase.trans (le_add_of_nonneg_right hsum)

lemma lrLowK_upper_by_LHead
    {beta A xi : ℝ} {n : ℕ}
    (hxi : xi ∈ Icc (0 : ℝ) 1)
    (hA : beta + lrLowLHead xi n ≤ A) :
    lrLowK beta xi lrLowB n ≤ (n : ℝ) * A := by
  have hterm : ∀ k ∈ Finset.range (n - 1),
      lrLowEtaWeight xi n k * (lrLowB (k + 1) / lrLowB n) ≤
        (n : ℝ) *
          (xi ^ (n - (k + 1)) /
            (2 * ((n - (k + 1) : ℕ) : ℝ))) := by
    intro k hk
    have hklt : k + 1 < n := by
      have := Finset.mem_range.mp hk
      omega
    have hjpos : (0 : ℝ) < k + 1 := by positivity
    have hrpos : (0 : ℝ) < (n - (k + 1) : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt hklt
    have hratio := lrLowB_ratio_le (j := k + 1) (n := n) (by omega) hklt.le
    norm_num only [Nat.cast_add, Nat.cast_one] at hratio
    have hw := lrLowEtaWeight_nonneg hxi.1 hk
    calc
      lrLowEtaWeight xi n k * (lrLowB (k + 1) / lrLowB n) ≤
          lrLowEtaWeight xi n k * ((n : ℝ) / (k + 1)) :=
        mul_le_mul_of_nonneg_left hratio hw
      _ = (n : ℝ) *
          (xi ^ (n - (k + 1)) /
            (2 * ((n - (k + 1) : ℕ) : ℝ))) := by
        unfold lrLowEtaWeight
        field_simp [hjpos.ne', hrpos.ne']
        push_cast
        ring
  have hsum := Finset.sum_le_sum hterm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold lrLowK
  unfold lrLowLHead at hA
  rw [← Finset.mul_sum] at hsum
  calc
    beta * (n : ℝ) +
          ∑ k ∈ Finset.range (n - 1),
            lrLowEtaWeight xi n k * (lrLowB (k + 1) / lrLowB n) ≤
        beta * (n : ℝ) +
          (n : ℝ) * ∑ k ∈ Finset.range (n - 1),
              (xi ^ (n - (k + 1)) /
                (2 * ((n - (k + 1) : ℕ) : ℝ))) := by
      linarith
    _ = (n : ℝ) *
        (beta + ∑ k ∈ Finset.range (n - 1),
          xi ^ (n - (k + 1)) /
            (2 * ((n - (k + 1) : ℕ) : ℝ))) := by ring
    _ ≤ (n : ℝ) * A := mul_le_mul_of_nonneg_left hA hn0

/-- The two `Kₙ` bounds instantiated with the analytic
`A = log(1+v) + L(vt)`. -/
theorem lrLowK_actual_bounds
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    lrFlowBeta v * lrLowH (v ^ 2 * t ^ 2) n ≤
        lrLowK (lrFlowBeta v) (v ^ 2 * t ^ 2) lrLowB n ∧
      lrLowK (lrFlowBeta v) (v ^ 2 * t ^ 2) lrLowB n ≤
        (n : ℝ) * (lrFlowBeta v + lrL (v * t)) := by
  have hvt : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have hxi : v ^ 2 * t ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · nlinarith [sq_pos_of_pos hvt]
    · have hs : (v * t) ^ 2 < 1 := (sq_lt_one_iff₀ hvt.le).2 hvtLt
      simpa [mul_pow] using hs
  have hbeta : 0 ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    exact Real.log_nonneg (by linarith [hv.1])
  constructor
  · exact lrLowK_lower hbeta ⟨hxi.1.le, hxi.2.le⟩
  · apply lrLowK_upper_by_LHead ⟨hxi.1.le, hxi.2.le⟩
    have hhead := lrLowLHead_le_lrL_sqrt hxi n
    have hsqrt : Real.sqrt (v ^ 2 * t ^ 2) = v * t := by
      rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_of_pos hvt]
    rw [hsqrt] at hhead
    linarith

end CourtadeKumar
