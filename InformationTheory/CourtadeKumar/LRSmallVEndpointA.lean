import InformationTheory.CourtadeKumar.LRSmallVGMonotone
import InformationTheory.CourtadeKumar.TopLogBound

/-!
# The endpoint `A` bound on the small-odds chart

For `0 < t ≤ 1`, the quantity
`A = log(1+v) + L(vt)` is bounded by `artanh(v)`, and hence is strictly
less than `1/2` when `v ≤ 1/3`.
-/

open Set

namespace CourtadeKumar

lemma lrFlowA_at_one_eq_artanh
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrFlowA v 1 = Real.artanh v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have hprod : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1, hv.2]
  rw [Real.artanh_eq_half_log
    (show v ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hv.1], hv.2.le⟩)]
  unfold lrFlowA lrFlowBeta lrL
  norm_num only [mul_one]
  rw [Real.log_div hp hm,
    show 1 - v ^ 2 = (1 - v) * (1 + v) by ring,
    Real.log_mul hm hp]
  ring

theorem lrFlowA_le_artanh
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    lrFlowA v t ≤ Real.artanh v := by
  have hvt0 : 0 ≤ v * t := mul_nonneg hv.1.le ht.1.le
  have hvtv : v * t ≤ v := by
    nlinarith [mul_nonneg hv.1.le (sub_nonneg.mpr ht.2)]
  have hL := lrL_mono_nonneg hvt0 hvtv hv.2
  rw [← lrFlowA_at_one_eq_artanh hv]
  unfold lrFlowA
  simpa using add_le_add_left hL (lrFlowBeta v)

theorem lrFlowA_lt_half_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioc (0 : ℝ) 1) :
    lrFlowA v t < 1 / 2 := by
  have hart := artanh_le_cubicPade
    (show v ∈ Icc (0 : ℝ) (1 / 3) from ⟨hv.1.le, hvSmall⟩)
  have hvSq : v ^ 2 ≤ (1 / 9 : ℝ) := by
    have hprod : 0 ≤ (1 / 3 : ℝ) - v := sub_nonneg.mpr hvSmall
    have hsum : 0 ≤ (1 / 3 : ℝ) + v := by linarith [hv.1]
    nlinarith [mul_nonneg hprod hsum]
  have hvCube : v ^ 3 ≤ (1 / 27 : ℝ) := by
    have hmul := mul_le_mul hvSq hvSmall hv.1.le (by norm_num : (0 : ℝ) ≤ 1 / 9)
    have hvd : v ^ 3 = v ^ 2 * v := by ring
    nlinarith
  have hden : (0 : ℝ) < 3 * (1 - v ^ 2) := by nlinarith
  have hfrac : v ^ 3 / (3 * (1 - v ^ 2)) ≤ (1 / 72 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hA := lrFlowA_le_artanh hv ht
  linarith

end CourtadeKumar
