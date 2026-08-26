import InformationTheory.CourtadeKumar.LRLowShapeUTailConnection

/-! Transfer of the uniform U-tail minorant to every actual second scalar
with index `n ≥ 6`. -/

open Set

namespace CourtadeKumar

lemma lrLowJLower_le_log_gap
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowJLower (t ^ 2) ≤ Real.log 2 - topPhi t := by
  have hphi := lrLow_topPhi_first_upper ht
  have hlog := lr_log_two_millionth_bounds.1
  unfold lrLowJLower lrLowPhiFirstUpper
  linarith

lemma lrLowH_six_eq_mul_geometricSix (xi : ℝ) :
    lrLowH xi 6 = xi * lrLowGeometricSix xi := by
  unfold lrLowGeometricSix lrLowH
  norm_num [Finset.sum_range_succ]
  ring

theorem lrLowUTailMinorant_nonneg_of_sq_le
    {v t : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ)) :
    0 ≤ lrLowUTailMinorant v (t ^ 2) := by
  have hz : (20 / 17 : ℝ) * t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have h := lrLowUTailMinorant_nonneg hv hz
  have hscale :
      (17 / 20 : ℝ) * ((20 / 17 : ℝ) * t ^ 2) = t ^ 2 := by
    ring
  rw [hscale] at h
  exact h

lemma lrLowUTailMinorant_le_core
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) {n : ℕ} (hn : 6 ≤ n) :
    lrLowUTailMinorant v (t ^ 2) ≤
      lrGShape t v - lrLowTailH v * lrLowB n -
        (lrFlowBeta v + lrL (v * t)) /
          (v * (1 + v) * lrLowGeometricSix (v ^ 2 * t ^ 2)) := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hJ := lrLowJLower_le_log_gap ht
  have hA := lrLowA_bounds hv
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hcoef : 0 ≤ (1 - v) / v :=
    div_nonneg (sub_nonneg.mpr hv.2.le) hv.1.le
  have hAlower := mul_le_mul_of_nonneg_left hA.1 hcoef
  have hB : lrLowB n ≤ lrLowBnUpper 6 :=
    (lrLowB_antitone hn).trans (lrLowBn_le_upper 6)
  have htail0 : 0 ≤ lrLowTailH v := by
    have hthree := lrLowTailH_ge_three
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩)
    linarith
  have hBscaled := mul_le_mul_of_nonneg_left hB htail0
  have hxi0 : 0 ≤ v ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg v) (sq_nonneg t)
  have hgeomPos : 0 < lrLowGeometricSix (v ^ 2 * t ^ 2) := by
    unfold lrLowGeometricSix
    norm_num [Finset.sum_range_succ]
    nlinarith [pow_nonneg hxi0 1, pow_nonneg hxi0 2,
      pow_nonneg hxi0 3, pow_nonneg hxi0 4, pow_nonneg hxi0 5]
  have hden : 0 < v * (1 + v) * lrLowGeometricSix (v ^ 2 * t ^ 2) :=
    mul_pos (mul_pos hv.1 (by linarith [hv.1])) hgeomPos
  have hAupper := div_le_div_of_nonneg_right hA.2 hden.le
  have hG := lrGShape_ge_tail_envelope hv ht
  unfold lrLowUTailMinorant
  linarith

lemma lrLowTail_correction_bound
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) {n : ℕ} (hn : 6 ≤ n) :
    4 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
        lrFlowM v * t ^ 2 * lrLowB n ≤
      lrLowH (v ^ 2 * t ^ 2) n *
        ((lrFlowBeta v + lrL (v * t)) /
          (v * (1 + v) * lrLowGeometricSix (v ^ 2 * t ^ 2))) := by
  have hA0 : 0 ≤ lrFlowBeta v + lrL (v * t) := by
    have hb : 0 ≤ lrFlowBeta v := by
      unfold lrFlowBeta
      exact Real.log_nonneg (by linarith [hv.1])
    have hL : 0 ≤ lrL (v * t) := lrL_nonneg
      (mul_nonneg hv.1.le ht.1.le) (by
        calc
          v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
          _ < 1 := by simpa using ht.2)
    exact add_nonneg hb hL
  have hn1 : 1 ≤ n := by omega
  have hbScaled := lrLowB_scaled_le_quarter hn1
  have hfourB : 4 * (n : ℝ) * lrLowB n ≤ 1 := by nlinarith
  have hB0 := (lrLowB_pos n).le
  have hM0 : 0 ≤ lrFlowM v := by
    unfold lrFlowM
    exact div_nonneg hv.1.le (by linarith [hv.1])
  have hMx0 : 0 ≤ lrFlowM v * t ^ 2 :=
    mul_nonneg hM0 (sq_nonneg t)
  have hvden : 0 < v * (1 + v) := mul_pos hv.1 (by linarith [hv.1])
  have hxi : v ^ 2 * t ^ 2 ≤ 1 := by
    have hvSq : v ^ 2 ≤ 1 := by
      nlinarith [mul_pos (sub_pos.mpr hv.2) (by linarith [hv.1] : 0 < 1 + v)]
    have htSq : t ^ 2 ≤ 1 := by
      nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    calc
      v ^ 2 * t ^ 2 ≤ 1 * 1 :=
        mul_le_mul hvSq htSq (sq_nonneg t) (by norm_num)
      _ = 1 := by norm_num
  have hMx : lrFlowM v * t ^ 2 =
      (v ^ 2 * t ^ 2) / (v * (1 + v)) := by
    unfold lrFlowM
    field_simp [hv.1.ne', (by linarith [hv.1] : 1 + v ≠ 0)]
  have hfourB0 : 0 ≤ 4 * (n : ℝ) * lrLowB n := by positivity
  have hxi0 : 0 ≤ v ^ 2 * t ^ 2 :=
    mul_nonneg (sq_nonneg v) (sq_nonneg t)
  have hsmall :
      (4 * (n : ℝ) * lrLowB n) * (lrFlowM v * t ^ 2) ≤
        (v ^ 2 * t ^ 2) / (v * (1 + v)) := by
    calc
      (4 * (n : ℝ) * lrLowB n) * (lrFlowM v * t ^ 2) ≤
          1 * (lrFlowM v * t ^ 2) :=
        mul_le_mul_of_nonneg_right hfourB hMx0
      _ = (v ^ 2 * t ^ 2) / (v * (1 + v)) := by simpa using hMx
  have hsmallA := mul_le_mul_of_nonneg_left hsmall hA0
  have hgeomPos : 0 < lrLowGeometricSix (v ^ 2 * t ^ 2) := by
    unfold lrLowGeometricSix
    norm_num [Finset.sum_range_succ]
    nlinarith [pow_nonneg hxi0 1, pow_nonneg hxi0 2,
      pow_nonneg hxi0 3, pow_nonneg hxi0 4, pow_nonneg hxi0 5]
  have hHmono := lrLowH_monotone
    (mul_nonneg (sq_nonneg v) (sq_nonneg t)) hn
  have hratio : v ^ 2 * t ^ 2 ≤
      lrLowH (v ^ 2 * t ^ 2) n /
        lrLowGeometricSix (v ^ 2 * t ^ 2) := by
    rw [le_div_iff₀ hgeomPos]
    rw [← lrLowH_six_eq_mul_geometricSix]
    exact hHmono
  have hAden0 : 0 ≤
      (lrFlowBeta v + lrL (v * t)) / (v * (1 + v)) :=
    div_nonneg hA0 hvden.le
  have hratioScaled := mul_le_mul_of_nonneg_right hratio hAden0
  calc
    4 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrFlowM v * t ^ 2 * lrLowB n =
        (lrFlowBeta v + lrL (v * t)) *
          ((4 * (n : ℝ) * lrLowB n) * (lrFlowM v * t ^ 2)) := by ring
    _ ≤ (lrFlowBeta v + lrL (v * t)) *
        ((v ^ 2 * t ^ 2) / (v * (1 + v))) := hsmallA
    _ = (v ^ 2 * t ^ 2) *
        ((lrFlowBeta v + lrL (v * t)) / (v * (1 + v))) := by ring
    _ ≤ (lrLowH (v ^ 2 * t ^ 2) n /
          lrLowGeometricSix (v ^ 2 * t ^ 2)) *
          ((lrFlowBeta v + lrL (v * t)) / (v * (1 + v))) := by
      simpa using hratioScaled
    _ = lrLowH (v ^ 2 * t ^ 2) n *
        ((lrFlowBeta v + lrL (v * t)) /
          (v * (1 + v) * lrLowGeometricSix (v ^ 2 * t ^ 2))) := by
      field_simp [hgeomPos.ne', hv.1.ne',
        (by linarith [hv.1] : 1 + v ≠ 0)]

theorem lrLowSecondScalar_tail_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ))
    {n : ℕ} (hn : 6 ≤ n) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) n *
          lrLowR v (t ^ 2) (lrGShape t v) n +
        2 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) n := by
  have hminorant := lrLowUTailMinorant_nonneg_of_sq_le
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) htSq
  have hcore := lrLowUTailMinorant_le_core hv ht hn
  have hcorr := lrLowTail_correction_bound hv ht hn
  have hH0 := lrLowH_nonneg
    (mul_nonneg (sq_nonneg v) (sq_nonneg t)) n
  have hP0 : 0 ≤ lrLowP v (t ^ 2) n := by
    have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
    have htClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    rw [← (lrLowP_hasSum hvClosed htClosed n).tsum_eq]
    exact tsum_nonneg (fun k ↦ mul_nonneg (lrLowA_pos (by omega)).le
      (lrLowT_nonneg hv.1.le (sq_nonneg t) _))
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hA0 : 0 ≤ lrFlowBeta v + lrL (v * t) := by
    have hb : 0 ≤ lrFlowBeta v := by
      unfold lrFlowBeta
      exact Real.log_nonneg (by linarith [hv.1])
    have hL : 0 ≤ lrL (v * t) := lrL_nonneg
      (mul_nonneg hv.1.le ht.1.le) (by
        calc
          v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
          _ < 1 := by simpa using ht.2)
    exact add_nonneg hb hL
  have hmain :
      0 ≤ lrLowH (v ^ 2 * t ^ 2) n *
          (lrGShape t v - lrLowTailH v * lrLowB n) -
        4 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrFlowM v * t ^ 2 * lrLowB n := by
    have hcoreScaled := mul_le_mul_of_nonneg_left hcore hH0
    have hminorantScaled := mul_nonneg hH0 hminorant
    linarith
  have hpositive : 0 ≤
      lrLowH (v ^ 2 * t ^ 2) n * lrLowP v (t ^ 2) n +
        2 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowP v (t ^ 2) n := by positivity
  unfold lrLowR lrLowEta
  nlinarith

end CourtadeKumar
