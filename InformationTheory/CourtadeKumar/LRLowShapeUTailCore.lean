import InformationTheory.CourtadeKumar.LRLowShapeTailData

/-! Lightweight analytic estimates for the uniform `n ≥ 6` tail.

This module isolates the endpoint estimate needed by the compact-`V`
certificate from the much larger low-shape polynomial certificate.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowQuarterTail (n : ℕ) : ℝ :=
  1 / (4 * (n : ℝ))

lemma lrLowQuarterTail_nonneg (n : ℕ) : 0 ≤ lrLowQuarterTail n := by
  unfold lrLowQuarterTail
  positivity

lemma lrLowQuarterTail_tendsto_zero :
    Filter.Tendsto lrLowQuarterTail Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun n ↦ lrLowQuarterTail_nonneg n)
    (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  cases n with
  | zero => norm_num [lrLowQuarterTail]
  | succ n =>
      unfold lrLowQuarterTail
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hleft : 0 < 4 * ((n : ℝ) + 1) := by positivity
      have hright : 0 < (n : ℝ) + 1 + 1 := by positivity
      rw [div_le_div_iff₀ hleft hright]
      nlinarith

lemma lrLowQuarterTail_diff_nonneg
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowQuarterTail n - lrLowQuarterTail (n + 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lrLowQuarterTail
  norm_num only [Nat.cast_add, Nat.cast_one]
  have h0 : 0 < 4 * (n : ℝ) := by positivity
  have h1 : 0 < 4 * ((n : ℝ) + 1) := by positivity
  rw [sub_nonneg, div_le_div_iff₀ h1 h0]
  nlinarith

lemma lrLowQuarterTail_diff_hasSum
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ ↦
      lrLowQuarterTail (k + n) - lrLowQuarterTail (k + n + 1))
      (lrLowQuarterTail n) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦
    lrLowQuarterTail_diff_nonneg (n := k + n) (by omega))]
  have hshift : Filter.Tendsto (fun m : ℕ ↦ lrLowQuarterTail (m + n))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat n).2 lrLowQuarterTail_tendsto_zero
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ lrLowQuarterTail n)
      Filter.atTop (nhds (lrLowQuarterTail n)) := tendsto_const_nhds
  have hlimit := hconst.sub hshift
  have hsum (m : ℕ) :
      ∑ k ∈ Finset.range m,
          (lrLowQuarterTail (k + n) - lrLowQuarterTail (k + n + 1)) =
        lrLowQuarterTail n - lrLowQuarterTail (m + n) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      Finset.sum_range_sub' (fun k ↦ lrLowQuarterTail (k + n)) m
  convert hlimit using 1
  · funext m
    exact hsum m
  · simp

lemma lrLowA_le_quarterTail_diff
    {m : ℕ} (hm : 1 ≤ m) :
    lrLowA (m + 1) ≤ lrLowQuarterTail m - lrLowQuarterTail (m + 1) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold lrLowA lrLowQuarterTail
  norm_num only [Nat.cast_add, Nat.cast_one]
  have h0 : 0 < (m : ℝ) := by positivity
  have h1 : 0 < (m : ℝ) + 1 := by positivity
  have h2 : 0 < 2 * ((m : ℝ) + 1) - 1 := by nlinarith
  field_simp [h0.ne', h1.ne', h2.ne']
  nlinarith

theorem lrLowB_le_quarterTail
    {n : ℕ} (hn : 1 ≤ n) :
    lrLowB n ≤ lrLowQuarterTail n := by
  have hb := lrLowB_hasSum n
  have hq := lrLowQuarterTail_diff_hasSum hn
  rw [← hb.tsum_eq, ← hq.tsum_eq]
  exact hb.summable.tsum_le_tsum (fun k ↦ by
    simpa [add_assoc] using
      lrLowA_le_quarterTail_diff (m := k + n) (by omega)) hq.summable

theorem lrLowB_scaled_le_quarter
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * lrLowB n ≤ 1 / 4 := by
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    (n : ℝ) * lrLowB n ≤ (n : ℝ) * lrLowQuarterTail n :=
      mul_le_mul_of_nonneg_left (lrLowB_le_quarterTail hn) hnR
    _ = 1 / 4 := by
      unfold lrLowQuarterTail
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hn0]

end CourtadeKumar
