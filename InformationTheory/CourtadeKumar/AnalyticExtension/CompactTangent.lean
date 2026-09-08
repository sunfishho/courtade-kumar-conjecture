import InformationTheory.CourtadeKumar.AnalyticExtension.CompactRestored
import Mathlib.Analysis.Convex.Deriv

/-! A global affine lower bound for both complete shape entropy terms. -/
open Set
namespace CourtadeKumar.LRAnalyticCompact

lemma phi_tangent {a z : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Icc (-1 : ℝ) 1) :
    topPhi a + Real.artanh a * (z - a) ≤ topPhi z := by
  have hda := hasDerivAt_topPhi ha
  have ha' : a ∈ Icc (-1 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  rcases lt_trichotomy z a with h | h | h
  · have hs := topPhi_convexOn.slope_le_of_hasDerivAt hz ha' h hda
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · subst z
    simp
  · have hs := topPhi_convexOn.le_slope_of_hasDerivAt ha' hz h hda
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

lemma shape_tangent {a b v t : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hv : 0 < v) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hvt : v * t ∈ Icc (-1 : ℝ) 1) :
    (Real.artanh a + Real.artanh b) * t +
      (Real.log (1 - b ^ 2) / 2) / v + Real.log (1 - a ^ 2) / 2 ≤
      topPhi t + topPhi (v * t) / v := by
  have h1 := phi_tangent ha ht
  have h2 := div_le_div_of_nonneg_right (phi_tangent hb hvt) hv.le
  have haid := mul_artanh_sub_topPhi_eq_lrL ha
  have hbid := mul_artanh_sub_topPhi_eq_lrL hb
  unfold lrL at haid hbid
  have heq : (topPhi b + Real.artanh b * (v * t - b)) / v =
      Real.artanh b * t + (Real.log (1 - b ^ 2) / 2) / v := by
    have hid : topPhi b - b * Real.artanh b = Real.log (1 - b ^ 2) / 2 := by linarith
    field_simp [hv.ne']
    nlinarith
  rw [heq] at h2
  nlinarith

theorem rational_shape_tangent {a b v t aT au ac : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hat : aT ≤ Real.artanh a + Real.artanh b)
    (hau : au ≤ Real.log (1 - b ^ 2) / 2)
    (hac : ac ≤ Real.log (1 - a ^ 2) / 2) :
    aT * t + au / v + ac ≤ topPhi t + topPhi (v * t) / v := by
  have hvt : v * t ∈ Icc (-1 : ℝ) 1 := by
    have hp := mul_pos hv.1 ht.1
    have hu := mul_lt_mul_of_pos_right hv.2 ht.1
    constructor <;> nlinarith [ht.2]
  have h := shape_tangent ha hb hv.1 ⟨by linarith [ht.1], ht.2.le⟩ hvt
  have h1 := mul_le_mul_of_nonneg_right hat ht.1.le
  have h2 := div_le_div_of_nonneg_right hau hv.1.le
  linarith

end CourtadeKumar.LRAnalyticCompact
