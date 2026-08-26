import InformationTheory.CourtadeKumar.LRLowShapeUL1Certificate

/-! Common analytic identities and one-sided finite data for the second
low-shape `U` scalar. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowPhiPrefix (v x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    lrLowA (k + 1) * lrLowT v x (k + 1)

noncomputable def lrLowBnUpper (n : ℕ) : ℝ :=
  (693148 : ℝ) / 1000000 -
    ∑ k ∈ Finset.range n, lrLowA (k + 1)

/-- Retain the terms `m=n+1,...,12`; the range is used only for `n≤12`. -/
noncomputable def lrLowPnLower (v x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (12 - n),
    lrLowA (k + n + 1) * lrLowT v x (k + n + 1)

lemma lrLowP_zero_eq_prefix_add
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    lrLowP v x 0 = lrLowPhiPrefix v x n + lrLowP v x n := by
  let f : ℕ → ℝ := fun k ↦
    lrLowA (k + 1) * lrLowT v x (k + 1)
  have hfull : HasSum f (lrLowP v x 0) := by
    simpa [f] using lrLowP_hasSum hv hx 0
  have hshift := (hasSum_nat_add_iff' n).2 hfull
  have htail := lrLowP_hasSum hv hx n
  have hshift' : HasSum (fun k : ℕ ↦
      lrLowA (k + n + 1) * lrLowT v x (k + n + 1))
      (lrLowP v x 0 - lrLowPhiPrefix v x n) := by
    simpa [f, lrLowPhiPrefix, add_assoc] using hshift
  have heq := hshift'.unique htail
  linarith

lemma lrGShape_add_p_eq_lower_prefix
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) (n : ℕ) :
    lrGShape t v + lrLowP v (t ^ 2) n =
      lrG v - lrLowPhiPrefix v (t ^ 2) n := by
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  have hsplit := lrLowP_zero_eq_prefix_add
    (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩) hx n
  rw [lrLowP_zero_eq_phi hv ht] at hsplit
  unfold lrGShape
  linarith

lemma lrLowBn_le_upper (n : ℕ) : lrLowB n ≤ lrLowBnUpper n := by
  have hlog := lr_log_two_millionth_bounds.2.le
  unfold lrLowB lrLowBnUpper
  linarith

lemma lrLowBnUpper_nonneg (n : ℕ) : 0 ≤ lrLowBnUpper n := by
  exact (lrLowB_pos n).le.trans (lrLowBn_le_upper n)

lemma lrLowPnLower_nonneg
    {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ lrLowPnLower v x n := by
  unfold lrLowPnLower
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (lrLowA_pos (by omega)).le (lrLowT_nonneg hv hx _)

lemma lrLowPnLower_le
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : n ≤ 12) :
    lrLowPnLower v x n ≤ lrLowP v x n := by
  have hp := lrLowP_hasSum hv hx n
  have hsum := hp.summable.sum_le_tsum (Finset.range (12 - n)) (fun k _ ↦
    mul_nonneg (lrLowA_pos (by omega)).le (lrLowT_nonneg hv.1 hx.1 _))
  rw [hp.tsum_eq] at hsum
  simpa [lrLowPnLower, add_assoc] using hsum

noncomputable def lrLowL12 (q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 12, q ^ (k + 1) / (2 * (k + 1))

noncomputable def lrLowL12Upper (q : ℝ) : ℝ :=
  lrLowL12 q + q ^ 13 / (26 * (1 - q))

noncomputable def lrLowALower (v x : ℝ) : ℝ :=
  lrLowBetaLower v + lrLowL12 (v ^ 2 * x)

noncomputable def lrLowAUpper (v x : ℝ) : ℝ :=
  lrAtanh5Upper (v / (2 + v)) + lrLowL12Upper (v ^ 2 * x)

lemma lrLow_sqrt_sq_product
    {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    Real.sqrt (v ^ 2 * t ^ 2) = v * t := by
  rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hv ht)]

lemma lrLowA_bounds
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    lrLowALower v (t ^ 2) ≤ lrFlowBeta v + lrL (v * t) ∧
      lrFlowBeta v + lrL (v * t) ≤ lrLowAUpper v (t ^ 2) := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hq0 : 0 < v ^ 2 * t ^ 2 := mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
  have hq1 : v ^ 2 * t ^ 2 < 1 := by
    have hvSq : v ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hv.2) (by linarith [hv.1] : 0 < 1 + v)]
    have htSq : t ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
    calc
      v ^ 2 * t ^ 2 ≤ v ^ 2 * 1 := mul_le_mul_of_nonneg_left htSq (sq_nonneg v)
      _ < 1 := by simpa using hvSq
  have hsqrt := lrLow_sqrt_sq_product hv.1.le ht.1.le
  have hLlower := lrL_sqrt_partial_sum_le
    (show v ^ 2 * t ^ 2 ∈ Ioo (0 : ℝ) 1 from ⟨hq0, hq1⟩) 12
  rw [hsqrt] at hLlower
  have hLupper := lrL_sqrt_tail_twelve_upper hq0 hq1
  rw [hsqrt] at hLupper
  have hbeta := lrAtanh5_beta_bounds hvIoc
  constructor
  · simpa [lrLowALower, lrLowL12, lrLowBetaLower, lrFlowBeta] using
      add_le_add hbeta.1 hLlower
  · have hLupper' : lrL (v * t) ≤
        (∑ n ∈ Finset.range 12,
          (v ^ 2 * t ^ 2) ^ (n + 1) / (2 * ((n : ℝ) + 1))) +
          (v ^ 2 * t ^ 2) ^ 13 / (26 * (1 - v ^ 2 * t ^ 2)) := by
      linarith [hLupper]
    simpa [lrLowAUpper, lrLowL12Upper, lrLowL12, lrFlowBeta] using
      add_le_add hbeta.2 hLupper'

end CourtadeKumar
