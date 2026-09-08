import InformationTheory.CourtadeKumar.AnalyticExtension.CompactRatio
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactRestored

/-! A short rational D lower bound and a polynomial exclusion of the J chart. -/
open Set
open scoped BigOperators
namespace CourtadeKumar.LRAnalyticCompact

noncomputable def dCoordinate (R v t : ℝ) : ℝ :=
  (1 - R) * (v ^ 2 * t ^ 2) / (2 - (1 + R) * (v ^ 2 * t ^ 2))

noncomputable def dPartial (M : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, q ^ (2 * j + 1) / (2 * (j : ℝ) + 1)

lemma flowB_formula {R v t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    lrFlowB R v t = Real.log (1 + v) - Real.log (1 - R * (v ^ 2 * t ^ 2)) / 2 := by
  have h := lrCompactVBFullX_eq_flowB (v := v) hR (sq_nonneg t)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht] at h
  unfold lrCompactVBFullX at h
  linarith

lemma flowD_formula {R v t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    lrFlowD R v t = (Real.log (1 - R * (v ^ 2 * t ^ 2)) -
      Real.log (1 - v ^ 2 * t ^ 2)) / 2 := by
  have h := lrCompactVDFullX_eq_flowD (v := v) hR (sq_nonneg t)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht] at h
  unfold lrCompactVDFullX at h
  linarith

lemma squared_shape_bounds {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ v ^ 2 * t ^ 2 ∧ v ^ 2 * t ^ 2 < 1 := by
  have hv2 : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
  have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  exact ⟨mul_nonneg (sq_nonneg v) (sq_nonneg t), by
    nlinarith [mul_lt_mul_of_pos_right hv2 (sq_pos_of_pos ht.1)]⟩

lemma coordinate_bounds {R v t : ℝ} (hR : R ∈ Icc (0 : ℝ) (9 / 10))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ dCoordinate R v t ∧ dCoordinate R v t < 1 := by
  have hy := squared_shape_bounds hv ht
  have hprod : (1 + R) * (v ^ 2 * t ^ 2) < 2 := by
    have h := mul_lt_mul_of_pos_left hy.2 (by linarith [hR.1] : 0 < 1 + R)
    nlinarith [hR.2]
  have hden : 0 < 2 - (1 + R) * (v ^ 2 * t ^ 2) := by linarith
  unfold dCoordinate
  constructor
  · exact div_nonneg (mul_nonneg (by linarith [hR.2]) hy.1) hden.le
  · rw [div_lt_one hden]
    nlinarith [hy.2]

lemma dPartial_nonneg (M : ℕ) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ dPartial M q := by
  unfold dPartial
  exact Finset.sum_nonneg (fun j _ => div_nonneg (pow_nonneg hq _) (by positivity))

theorem dPartial_le_flowD (M : ℕ) {R v t : ℝ}
    (hR : R ∈ Icc (0 : ℝ) (9 / 10))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    dPartial M (dCoordinate R v t) ≤ lrFlowD R v t := by
  have hq := coordinate_bounds hR hv ht
  have hy := squared_shape_bounds hv ht
  let y := v ^ 2 * t ^ 2
  have hy1 : 0 < 1 - y := by dsimp [y]; linarith [hy.2]
  have hRy : 0 < 1 - R * y := by
    have h := mul_le_mul_of_nonneg_right (show R ≤ 1 by linarith [hR.2]) hy.1
    dsimp [y]
    nlinarith [hy.2]
  have hden : 0 < 2 - (1 + R) * y := by
    have h := mul_lt_mul_of_pos_left hy.2 (by linarith [hR.1] : 0 < 1 + R)
    dsimp [y]
    nlinarith [hR.2]
  have hratio : (1 + dCoordinate R v t) / (1 - dCoordinate R v t) = (1 - R * y) / (1 - y) := by
    apply (div_eq_div_iff (sub_pos.mpr hq.2).ne' hy1.ne').2
    unfold dCoordinate
    change (1 + (1 - R) * y / (2 - (1 + R) * y)) * (1 - y) =
      (1 - R * y) * (1 - (1 - R) * y / (2 - (1 + R) * y))
    have hcancel : ((1 - R) * y / (2 - (1 + R) * y)) *
        (2 - (1 + R) * y) = (1 - R) * y := div_mul_cancel₀ _ hden.ne'
    nlinarith only [hcancel]
  have h := Real.sum_range_le_log_div hq.1 hq.2 M
  rw [hratio, Real.log_div hRy.ne' hy1.ne'] at h
  rw [flowD_formula hR.1 ht.1.le]
  simpa [dPartial, y, div_eq_mul_inv, mul_comm] using h

theorem j_nonpositive_of_polynomial {R v t : ℝ}
    (hR : R ∈ Icc (0 : ℝ) (9 / 10))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hpoly : (1 + v) ^ 2 * (1 - v ^ 2 * t ^ 2) ≤
      (1 - R * (v ^ 2 * t ^ 2)) ^ 2) :
    lrFlowJ R v t ≤ 0 := by
  have hy := squared_shape_bounds hv ht
  have hp : 0 < 1 + v := by linarith [hv.1]
  have h1y : 0 < 1 - v ^ 2 * t ^ 2 := by linarith [hy.2]
  have h1Ry : 0 < 1 - R * (v ^ 2 * t ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (show R ≤ 1 by linarith [hR.2]) hy.1
    nlinarith [hy.2]
  have hlog := Real.log_le_log (mul_pos (sq_pos_of_pos hp) h1y) hpoly
  rw [Real.log_mul (sq_pos_of_pos hp).ne' h1y.ne', Real.log_pow, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hDB : lrFlowB R v t ≤ lrFlowD R v t := by
    rw [flowB_formula hR.1 ht.1.le, flowD_formula hR.1 ht.1.le]
    linarith
  have hB : 0 ≤ lrFlowB R v t := by
    rw [flowB_formula hR.1 ht.1.le]
    have hpos := Real.log_nonneg (by linarith [hv.1] : 1 ≤ 1 + v)
    have hneg := Real.log_nonpos h1Ry.le (by nlinarith [mul_nonneg hR.1 hy.1])
    linarith
  have hmul := mul_le_mul_of_nonneg_left (show t ^ 2 ≤ 1 by nlinarith [ht.1, ht.2]) hB
  unfold lrFlowJ
  nlinarith

end CourtadeKumar.LRAnalyticCompact
