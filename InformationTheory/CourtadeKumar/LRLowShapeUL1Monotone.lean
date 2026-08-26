import InformationTheory.CourtadeKumar.LRLowShapeUL1Bridge

/-! A small analytic reduction of the bivariate `L₁` certificate.  The
minorant decreases in `x`, so only the edge `x=17/20` remains for exact
certification.  This replaces a 546-entry tensor table by a 41-entry
univariate certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowShapeX : ℝ := 17 / 20

noncomputable def lrLowP1Slope : ℝ :=
  ∑ k ∈ Finset.range 11,
    (k + 2 : ℝ) * lrLowA (k + 2) * lrLowShapeX ^ (k + 1)

lemma lr_pow_sub_pow_le
    {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (hxX : x ≤ X) (n : ℕ) :
    X ^ n - x ^ n ≤ (n : ℝ) * X ^ (n - 1) * (X - x) := by
  have hpow : x ^ n ≤ X ^ n := pow_le_pow_left₀ hx hxX n
  have habs := abs_pow_sub_pow_le X x n
  rw [abs_of_nonneg (sub_nonneg.mpr hpow),
    abs_of_nonneg (sub_nonneg.mpr hxX), abs_of_nonneg hX,
    abs_of_nonneg hx, max_eq_left hxX] at habs
  simpa [mul_assoc, mul_comm, mul_left_comm] using habs

lemma lrLowT_difference_le_slope
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) lrLowShapeX) (k : ℕ) :
    lrLowA (k + 2) *
        (lrLowT v lrLowShapeX (k + 2) - lrLowT v x (k + 2)) ≤
      ((k + 2 : ℝ) * lrLowA (k + 2) * lrLowShapeX ^ (k + 1)) *
        (1 + v) * (lrLowShapeX - x) := by
  have hX0 : 0 ≤ lrLowShapeX := by norm_num [lrLowShapeX]
  have hpow := lr_pow_sub_pow_le hx.1 hX0 hx.2 (k + 2)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hpow
  rw [show k + 2 - 1 = k + 1 by omega] at hpow
  have hvpow : v ^ (2 * (k + 2) - 1) ≤ v := by
    have h := pow_le_pow_of_le_one hv.1 hv.2
      (show 1 ≤ 2 * (k + 2) - 1 by omega)
    simpa using h
  have hvfactor0 : 0 ≤ 1 + v ^ (2 * (k + 2) - 1) :=
    add_nonneg (by norm_num) (pow_nonneg hv.1 _)
  have hxgap0 : 0 ≤ lrLowShapeX - x := sub_nonneg.mpr hx.2
  have hslope0 : 0 ≤ (k + 2 : ℝ) * lrLowShapeX ^ (k + 1) := by positivity
  have hcombined :
      (lrLowShapeX ^ (k + 2) - x ^ (k + 2)) *
          (1 + v ^ (2 * (k + 2) - 1)) ≤
        ((k + 2 : ℝ) * lrLowShapeX ^ (k + 1)) *
          (1 + v) * (lrLowShapeX - x) := by
    calc
      (lrLowShapeX ^ (k + 2) - x ^ (k + 2)) *
          (1 + v ^ (2 * (k + 2) - 1)) ≤
          ((k + 2 : ℝ) * lrLowShapeX ^ (k + 1) *
            (lrLowShapeX - x)) *
              (1 + v ^ (2 * (k + 2) - 1)) :=
        mul_le_mul_of_nonneg_right hpow hvfactor0
      _ ≤ ((k + 2 : ℝ) * lrLowShapeX ^ (k + 1) *
            (lrLowShapeX - x)) * (1 + v) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hvpow])
          (mul_nonneg hslope0 hxgap0)
      _ = ((k + 2 : ℝ) * lrLowShapeX ^ (k + 1)) *
          (1 + v) * (lrLowShapeX - x) := by ring
  have ha0 := (lrLowA_pos (by omega : 1 ≤ k + 2)).le
  unfold lrLowT
  have hid :
      lrLowShapeX ^ (k + 2) * (1 + v ^ (2 * (k + 2) - 1)) -
          x ^ (k + 2) * (1 + v ^ (2 * (k + 2) - 1)) =
        (lrLowShapeX ^ (k + 2) - x ^ (k + 2)) *
          (1 + v ^ (2 * (k + 2) - 1)) := by ring
  rw [hid]
  convert mul_le_mul_of_nonneg_left hcombined ha0 using 1 <;> ring

lemma lrLowP1Lower_difference_le
    {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) lrLowShapeX) :
    lrLowP1Lower v lrLowShapeX - lrLowP1Lower v x ≤
      lrLowP1Slope * (1 + v) * (lrLowShapeX - x) := by
  unfold lrLowP1Lower
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ k ∈ Finset.range 11,
        (lrLowA (k + 2) * lrLowT v lrLowShapeX (k + 2) -
          lrLowA (k + 2) * lrLowT v x (k + 2)) ≤
      ∑ k ∈ Finset.range 11,
        ((k + 2 : ℝ) * lrLowA (k + 2) * lrLowShapeX ^ (k + 1)) *
          (1 + v) * (lrLowShapeX - x) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [mul_sub] using lrLowT_difference_le_slope hv hx k
    _ = lrLowP1Slope * (1 + v) * (lrLowShapeX - x) := by
      unfold lrLowP1Slope
      rw [Finset.sum_mul, Finset.sum_mul]

lemma lrLowP1Slope_nonneg : 0 ≤ lrLowP1Slope := by
  unfold lrLowP1Slope
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg
    (mul_nonneg (by positivity) (lrLowA_pos (by omega)).le)
    (pow_nonneg (by norm_num [lrLowShapeX]) _)

lemma lrLowP1Slope_log_bound :
    2 * ((693148 : ℝ) / 1000000) * lrLowP1Slope ≤ 1 / 2 := by
  norm_num [lrLowP1Slope, lrLowShapeX, lrLowA, Finset.sum_range_succ]

lemma lrLowBetaLower_le_log_upper
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowBetaLower v ≤ (693148 : ℝ) / 1000000 := by
  have hbeta := (lrAtanh5_beta_bounds hv).1
  have hlogTwo : Real.log (1 + v) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])
  exact hbeta.trans (hlogTwo.trans lr_log_two_millionth_bounds.2.le)

/-- Monotonicity in the shape variable, proved without a bivariate table. -/
theorem lrLowL1Minorant_edge_le
    {v x : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) lrLowShapeX) :
    lrLowL1Minorant v lrLowShapeX ≤ lrLowL1Minorant v x := by
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
  have hpDiff := lrLowP1Lower_difference_le hvClosed hx
  have hbeta0 := lrLowBetaLower_nonneg hv
  have hbetaUpper := lrLowBetaLower_le_log_upper hv
  have hcoef : 2 * lrLowBetaLower v * lrLowP1Slope ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hbetaUpper lrLowP1Slope_nonneg
    nlinarith [lrLowP1Slope_log_bound, mul_nonneg hbeta0 lrLowP1Slope_nonneg]
  have hcommon0 : 0 ≤ (1 + v) * (lrLowShapeX - x) :=
    mul_nonneg (by linarith [hv.1]) (sub_nonneg.mpr hx.2)
  have hpScaled :
      2 * lrLowBetaLower v *
          (lrLowP1Lower v lrLowShapeX - lrLowP1Lower v x) ≤
        (1 / 2) * (1 + v) * (lrLowShapeX - x) := by
    calc
      2 * lrLowBetaLower v *
          (lrLowP1Lower v lrLowShapeX - lrLowP1Lower v x) ≤
          2 * lrLowBetaLower v *
            (lrLowP1Slope * (1 + v) * (lrLowShapeX - x)) :=
        mul_le_mul_of_nonneg_left hpDiff (mul_nonneg (by norm_num) hbeta0)
      _ = (2 * lrLowBetaLower v * lrLowP1Slope) *
          ((1 + v) * (lrLowShapeX - x)) := by ring
      _ ≤ (1 / 2) * ((1 + v) * (lrLowShapeX - x)) :=
        mul_le_mul_of_nonneg_right hcoef hcommon0
      _ = (1 / 2) * (1 + v) * (lrLowShapeX - x) := by ring
  have hbetaPlus0 : 0 ≤ lrAtanh5Upper (v / (2 + v)) :=
    (show 0 ≤ lrFlowBeta v by
      unfold lrFlowBeta
      exact Real.log_nonneg (by linarith [hv.1])).trans
        (by simpa [lrFlowBeta] using (lrAtanh5_beta_bounds hv).2)
  have hM0 : 0 ≤ lrFlowM v := by
    unfold lrFlowM
    exact div_nonneg hv.1.le (by linarith [hv.1])
  have htailGain : 0 ≤
      2 * lrAtanh5Upper (v / (2 + v)) * (2 * lrFlowM v) *
        (lrLowShapeX - x) * lrLowB1Upper := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (mul_nonneg (by norm_num) hM0))
        (sub_nonneg.mpr hx.2))
      lrLowB1Upper_nonneg
  have hTOneX : lrLowT v lrLowShapeX 1 = lrLowShapeX * (1 + v) := by
    unfold lrLowT
    norm_num
  have hTOnex : lrLowT v x 1 = x * (1 + v) := by
    unfold lrLowT
    norm_num
  have haOne : lrLowA 1 = 1 / 2 := by norm_num [lrLowA]
  unfold lrLowL1Minorant
  rw [hTOneX, hTOnex, haOne]
  nlinarith [hpScaled, htailGain]

end CourtadeKumar
