import InformationTheory.CourtadeKumar.LRLowShapeUGLower

/-! Bridge from the finite rational head minorants `𝓦ₙ` to the actual
second scalar in the low-shape `U` reduction. -/

open Set

namespace CourtadeKumar

noncomputable def lrLowWMinorant (v x : ℝ) (n : ℕ) : ℝ :=
  lrLowH (v ^ 2 * x) n *
      (lrLowGLower v - lrLowPhiPrefix v x n -
        lrLowTailH v * lrLowBnUpper n) +
    2 * n * lrLowALower v x * lrLowPnLower v x n -
    2 * n * lrLowAUpper v x * (2 * lrFlowM v * x) * lrLowBnUpper n

lemma lrLowL12_nonneg
    {q : ℝ} (hq : 0 ≤ q) : 0 ≤ lrLowL12 q := by
  unfold lrLowL12
  apply Finset.sum_nonneg
  intro k hk
  exact div_nonneg (pow_nonneg hq _) (by positivity)

lemma lrLowALower_nonneg
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hx : 0 ≤ x) :
    0 ≤ lrLowALower v x := by
  unfold lrLowALower
  exact add_nonneg (lrLowBetaLower_nonneg hv)
    (lrLowL12_nonneg (mul_nonneg (sq_nonneg v) hx))

theorem lrLowWMinorant_le_second_scalar
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) {n : ℕ} (hn : n ≤ 12) :
    lrLowWMinorant v (t ^ 2) n ≤
      lrLowH (v ^ 2 * t ^ 2) n *
          lrLowR v (t ^ 2) (lrGShape t v) n +
        2 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) n := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hsplit := lrGShape_add_p_eq_lower_prefix hv
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩) n
  have hg := lrLowGLower_le_lrG hvIoc
  have hb := lrLowBn_le_upper n
  have hb0 := (lrLowB_pos n).le
  have hbUpper0 := lrLowBnUpper_nonneg n
  have hp := lrLowPnLower_le hvClosed hx hn
  have hpLower0 := lrLowPnLower_nonneg hvClosed.1 hx.1 n
  have hp0 : 0 ≤ lrLowP v (t ^ 2) n := hpLower0.trans hp
  have hA := lrLowA_bounds hv
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hActualA0 : 0 ≤ lrFlowBeta v + lrL (v * t) := by
    have hbeta : 0 ≤ lrFlowBeta v := by
      unfold lrFlowBeta
      exact Real.log_nonneg (by linarith [hv.1])
    have hL : 0 ≤ lrL (v * t) := lrL_nonneg
      (mul_nonneg hv.1.le ht.1.le) (by
        calc
          v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
          _ < 1 := by simpa using ht.2)
    exact add_nonneg hbeta hL
  have hALower0 := lrLowALower_nonneg hvIoc hx.1
  have hAUpper0 : 0 ≤ lrLowAUpper v (t ^ 2) :=
    hActualA0.trans hA.2
  have hh := lrLowTailH_ge_three hvClosed
  have hh0 : 0 ≤ lrLowTailH v := by linarith
  have hH0 := lrLowH_nonneg
    (mul_nonneg (sq_nonneg v) hx.1) n
  have hd0 : 0 ≤ 2 * lrFlowM v * t ^ 2 := by
    unfold lrFlowM
    exact mul_nonneg
      (mul_nonneg (by norm_num) (div_nonneg hv.1.le (by linarith [hv.1])))
      (sq_nonneg t)
  have hheadInside :
      lrLowGLower v - lrLowPhiPrefix v (t ^ 2) n -
          lrLowTailH v * lrLowBnUpper n ≤
        lrG v - lrLowPhiPrefix v (t ^ 2) n -
          lrLowTailH v * lrLowB n := by
    have hbScaled := mul_le_mul_of_nonneg_left hb hh0
    linarith
  have hhead := mul_le_mul_of_nonneg_left hheadInside hH0
  have hpositive :
      lrLowALower v (t ^ 2) * lrLowPnLower v (t ^ 2) n ≤
        (lrFlowBeta v + lrL (v * t)) * lrLowP v (t ^ 2) n :=
    mul_le_mul hA.1 hp hpLower0 hActualA0
  have hnegative :
      (lrFlowBeta v + lrL (v * t)) * (2 * lrFlowM v * t ^ 2) * lrLowB n ≤
        lrLowAUpper v (t ^ 2) * (2 * lrFlowM v * t ^ 2) *
          lrLowBnUpper n := by
    have hfirst := mul_le_mul_of_nonneg_right hA.2 hd0
    exact mul_le_mul hfirst hb hb0 (mul_nonneg hAUpper0 hd0)
  unfold lrLowWMinorant lrLowR lrLowEta
  rw [hsplit]
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2n : 0 ≤ 2 * (n : ℝ) := mul_nonneg (by norm_num) hn0
  have hpositiveScaled := mul_le_mul_of_nonneg_left hpositive h2n
  have hnegativeScaled := mul_le_mul_of_nonneg_left hnegative h2n
  nlinarith [hhead, hpositiveScaled, hnegativeScaled]

end CourtadeKumar
