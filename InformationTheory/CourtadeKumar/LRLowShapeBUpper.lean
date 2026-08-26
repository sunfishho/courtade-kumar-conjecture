import InformationTheory.CourtadeKumar.LRLowShapeVScalarClosure

/-! A rational upper envelope for the endpoint tails `b_j`.

The envelope is the cubic Taylor majorant used in the supplied proof.  The
argument below verifies its discrete derivative directly and then compares
the two convergent positive series.  In particular, this module introduces no
finite-computation shortcut.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowBUpper (j : ℕ) : ℝ :=
  1 / (2 * (2 * (j : ℝ) + 1)) +
  1 / (4 * (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2)) +
  1 / (4 * (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2) *
    (2 * (j : ℝ) + 3)) +
  3 / (8 * (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2) *
    (2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 4)) +
  3 / (2 * (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2) *
    (2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 4) *
    (2 * (j : ℝ) + 5))

lemma lrLowBUpper_nonneg (j : ℕ) : 0 ≤ lrLowBUpper j := by
  unfold lrLowBUpper
  positivity

lemma lrLowBUpper_diff_ge_A (j : ℕ) :
    lrLowA (j + 1) ≤ lrLowBUpper j - lrLowBUpper (j + 1) := by
  unfold lrLowA lrLowBUpper
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  ring_nf
  have hd : 0 < 1 + (j : ℝ) * 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hd
  field_simp
  ring_nf
  nlinarith [pow_nonneg hj 2, pow_nonneg hj 3, pow_nonneg hj 4,
    pow_nonneg hj 5]

lemma lrLowBUpper_le_simple (j : ℕ) :
    lrLowBUpper j ≤ 3 / ((j : ℝ) + 1) := by
  unfold lrLowBUpper
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  ring_nf
  rw [← sub_nonneg]
  ring_nf
  positivity

lemma lrLowBUpper_tendsto_zero :
    Filter.Tendsto lrLowBUpper Filter.atTop (nhds 0) := by
  apply squeeze_zero (lrLowBUpper_nonneg) (lrLowBUpper_le_simple)
  have hbase :
      Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := hbase.const_mul 3
  convert h using 1
  · funext n
    ring_nf
  · ring_nf

lemma lrLowBUpper_diff_hasSum (j : ℕ) :
    HasSum (fun k : ℕ ↦
      lrLowBUpper (k + j) - lrLowBUpper (k + j + 1))
      (lrLowBUpper j) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k ↦ (lrLowA_pos (by omega)).le.trans
      (lrLowBUpper_diff_ge_A (k + j)))]
  have hshift : Filter.Tendsto (fun n : ℕ ↦ lrLowBUpper (n + j))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat j).2 lrLowBUpper_tendsto_zero
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ lrLowBUpper j)
      Filter.atTop (nhds (lrLowBUpper j)) := tendsto_const_nhds
  have hlim := hconst.sub hshift
  have hsum (n : ℕ) :
      ∑ i ∈ Finset.range n,
          (lrLowBUpper (i + j) - lrLowBUpper (i + j + 1)) =
        lrLowBUpper j - lrLowBUpper (n + j) := by
    simpa [add_assoc, add_comm, add_left_comm] using
      Finset.sum_range_sub' (fun i ↦ lrLowBUpper (i + j)) n
  convert hlim using 1
  · funext n
    exact hsum n
  · simp

theorem lrLowB_le_upper (j : ℕ) : lrLowB j ≤ lrLowBUpper j := by
  have hb := lrLowB_hasSum j
  have hu := lrLowBUpper_diff_hasSum j
  rw [← hb.tsum_eq, ← hu.tsum_eq]
  exact hb.summable.tsum_le_tsum (fun k ↦
    lrLowBUpper_diff_ge_A (k + j)) hu.summable

end CourtadeKumar
