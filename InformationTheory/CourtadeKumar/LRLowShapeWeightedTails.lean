import InformationTheory.CourtadeKumar.LRLowShapeTailData

/-! Weighted `Tₙ` tails and their decreasing tail averages. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowT (v x : ℝ) (m : ℕ) : ℝ :=
  x ^ m * (1 + v ^ (2 * m - 1))

noncomputable def lrLowP (v x : ℝ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, lrLowA (k + j + 1) * lrLowT v x (k + j + 1)

lemma lrLowT_nonneg
    {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (m : ℕ) :
    0 ≤ lrLowT v x m := by
  unfold lrLowT
  positivity

lemma lrLowT_le_two
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    lrLowT v x m ≤ 2 := by
  have hxpow : x ^ m ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hvpow : v ^ (2 * m - 1) ≤ 1 := pow_le_one₀ hv.1 hv.2
  have hxpow0 := pow_nonneg hx.1 m
  have hvpow0 := pow_nonneg hv.1 (2 * m - 1)
  unfold lrLowT
  nlinarith [mul_le_mul hxpow (by linarith [hvpow])
    (by linarith [hvpow0]) (by norm_num : (0 : ℝ) ≤ 1)]

lemma lrLowT_antitone_on_positive
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    lrLowT v x n ≤ lrLowT v x m := by
  have hxpow := pow_le_pow_of_le_one hx.1 hx.2 hmn
  have hexp : 2 * m - 1 ≤ 2 * n - 1 := by omega
  have hvpow := pow_le_pow_of_le_one hv.1 hv.2 hexp
  have hxNonneg := pow_nonneg hx.1 m
  have hvNonneg := pow_nonneg hv.1 (2 * n - 1)
  unfold lrLowT
  exact mul_le_mul hxpow (by linarith [hvpow])
    (by linarith [hvNonneg]) hxNonneg

lemma summable_lrLowP
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    Summable (fun k : ℕ ↦
      lrLowA (k + j + 1) * lrLowT v x (k + j + 1)) := by
  have hb := (lrLowB_hasSum j).summable.mul_left 2
  apply Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (lrLowA_pos (by omega)).le
        (lrLowT_nonneg hv.1 hx.1 _)) _ hb
  intro k
  have ha := (lrLowA_pos (by omega : 1 ≤ k + j + 1)).le
  have hT := lrLowT_le_two hv hx (k + j + 1)
  nlinarith

theorem lrLowP_hasSum
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    HasSum (fun k : ℕ ↦
      lrLowA (k + j + 1) * lrLowT v x (k + j + 1))
      (lrLowP v x j) := by
  exact (summable_lrLowP hv hx j).hasSum

lemma lrLowP_recursion
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    lrLowP v x j =
      lrLowA (j + 1) * lrLowT v x (j + 1) + lrLowP v x (j + 1) := by
  have hj := lrLowP_hasSum hv hx j
  have hshift := (hasSum_nat_add_iff' 1).2 hj
  have hnext := lrLowP_hasSum hv hx (j + 1)
  have hshift' : HasSum (fun k : ℕ ↦
      lrLowA (k + (j + 1) + 1) * lrLowT v x (k + (j + 1) + 1))
      (lrLowP v x j - lrLowA (j + 1) * lrLowT v x (j + 1)) := by
    convert hshift using 1
    · funext k
      congr 2 <;> omega
    · simp
  have heq := hshift'.unique hnext
  linarith

/-- Every weighted tail average is bounded by its first weight. -/
lemma lrLowP_le_first_mul_B
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    lrLowP v x j ≤ lrLowT v x (j + 1) * lrLowB j := by
  have hp := lrLowP_hasSum hv hx j
  have hb := (lrLowB_hasSum j).mul_left (lrLowT v x (j + 1))
  rw [← hp.tsum_eq, ← hb.tsum_eq]
  exact hp.summable.tsum_le_tsum (fun k ↦ by
    have ha := (lrLowA_pos (by omega : 1 ≤ k + j + 1)).le
    have hT := lrLowT_antitone_on_positive hv hx (by omega)
      (show j + 1 ≤ k + j + 1 by omega)
    nlinarith) hb.summable

lemma lrLowP_average_step
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    lrLowP v x (j + 1) / lrLowB (j + 1) ≤
      lrLowP v x j / lrLowB j := by
  have hpBound := lrLowP_le_first_mul_B hv hx (j + 1)
  have hT := lrLowT_antitone_on_positive hv hx (by omega : 1 ≤ j + 1)
    (by omega : j + 1 ≤ j + 2)
  have hpRec := lrLowP_recursion hv hx j
  have hbRec := lrLowB_recursion j
  have hb0 := lrLowB_pos j
  have hb1 := lrLowB_pos (j + 1)
  have ha := lrLowA_pos (by omega : 1 ≤ j + 1)
  rw [div_le_div_iff₀ hb1 hb0]
  have havg : lrLowP v x (j + 1) ≤
      lrLowT v x (j + 1) * lrLowB (j + 1) := by
    exact hpBound.trans (mul_le_mul_of_nonneg_right hT (lrLowB_pos _).le)
  have hscaled := mul_le_mul_of_nonneg_left havg ha.le
  rw [hpRec, hbRec]
  nlinarith

/-- The weighted tail averages `p_j/b_j` decrease with the cutoff. -/
theorem lrLowP_average_antitone
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Antitone (fun j : ℕ ↦ lrLowP v x j / lrLowB j) := by
  exact antitone_nat_of_succ_le (lrLowP_average_step hv hx)

/-- Subtracting a common scalar from the tail averages gives precisely the
comparison needed for `η_j = p_j - d b_j`. -/
theorem lrLowEta_tail_average
    {v x d : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) {j n : ℕ} (hjn : j ≤ n) :
    lrLowB j / lrLowB n * (lrLowP v x n - d * lrLowB n) ≤
      lrLowP v x j - d * lrLowB j := by
  have havg := lrLowP_average_antitone hv hx hjn
  have hbj := lrLowB_pos j
  have hbn := lrLowB_pos n
  change lrLowP v x n / lrLowB n ≤ lrLowP v x j / lrLowB j at havg
  rw [div_le_div_iff₀ hbn hbj] at havg
  field_simp [hbn.ne']
  nlinarith

end CourtadeKumar
