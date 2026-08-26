import InformationTheory.CourtadeKumar.LRLowShapeVH1Certificate
import InformationTheory.CourtadeKumar.LRLowShapeVH2Certificate
import InformationTheory.CourtadeKumar.LRLowShapeVH3Certificate
import InformationTheory.CourtadeKumar.LRLowShapeVH4Certificate
import InformationTheory.CourtadeKumar.LRLowShapeVH5Certificate

/-! Analytic dominance of the certified finite low-shape `V` heads. -/

open Set

namespace CourtadeKumar

theorem lrLowVHeadMinorant_le_coefficient
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    {n : ℕ} (hn2 : 2 ≤ n) (hn7 : n ≤ 7)
    (hGlow : 0 ≤ lrLowGShapeLower v (t ^ 2)) :
    lrLowVHeadMinorant v (t ^ 2) n ≤
      lrLowVConvolutionCoeff v t (n - 1) := by
  have hcomparison := lrLowVComparisonMinorant_le hv ht hn2 hn7 hGlow
  have hvClosed : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  have hxClosed : t ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg t
    · nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hp := lrLowPnLower_le hvClosed hxClosed (show n ≤ 12 by omega)
  have hp0 := lrLowPnLower_nonneg hv.1.le (sq_nonneg t) n
  have hA := lrLowA_bounds hv ⟨ht.1, ht.2.le⟩
  have hALower0 := lrLowALower_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) (sq_nonneg t)
  have hA0 : 0 ≤ lrFlowA v t := by
    unfold lrFlowA
    exact hALower0.trans hA.1
  have hpositive :
      lrLowALower v (t ^ 2) * lrLowPnLower v (t ^ 2) n ≤
        lrFlowA v t * lrLowP v (t ^ 2) n :=
    mul_le_mul hA.1 hp hp0 hA0
  have hpositiveScaled := mul_le_mul_of_nonneg_left hpositive (Nat.cast_nonneg n)
  have hid := lrLowVConvolutionCoeff_pred_eq_comparison
    (v := v) (t := t) ht.1.le (n := n) hn2
  unfold lrLowVHeadMinorant
  rw [hid]
  linarith

theorem lrLowVConvolutionCoeff_one_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVConvolutionCoeff v t 1 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hGlow := lrLowGShapeLower_nonneg hvIoc hxIcc
  have hminorant := lrLowVHeadMinorant_two_nonneg hvIoc hxIcc
  have hle := lrLowVHeadMinorant_le_coefficient hv ht
    (n := 2) (by norm_num) (by norm_num) hGlow
  norm_num at hle
  exact hminorant.trans hle

theorem lrLowVConvolutionCoeff_two_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVConvolutionCoeff v t 2 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hGlow := lrLowGShapeLower_nonneg hvIoc hxIcc
  have hminorant := lrLowVHeadMinorant_three_nonneg hvIoc hxIcc
  have hle := lrLowVHeadMinorant_le_coefficient hv ht
    (n := 3) (by norm_num) (by norm_num) hGlow
  norm_num at hle
  exact hminorant.trans hle

theorem lrLowVConvolutionCoeff_three_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVConvolutionCoeff v t 3 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hGlow := lrLowGShapeLower_nonneg hvIoc hxIcc
  have hminorant := lrLowVHeadMinorant_four_nonneg hvIoc hxIcc
  have hle := lrLowVHeadMinorant_le_coefficient hv ht
    (n := 4) (by norm_num) (by norm_num) hGlow
  norm_num at hle
  exact hminorant.trans hle

theorem lrLowVConvolutionCoeff_four_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVConvolutionCoeff v t 4 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hGlow := lrLowGShapeLower_nonneg hvIoc hxIcc
  have hminorant := lrLowVHeadMinorant_five_nonneg hvIoc hxIcc
  have hle := lrLowVHeadMinorant_le_coefficient hv ht
    (n := 5) (by norm_num) (by norm_num) hGlow
  norm_num at hle
  exact hminorant.trans hle

theorem lrLowVConvolutionCoeff_five_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVConvolutionCoeff v t 5 := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hGlow := lrLowGShapeLower_nonneg hvIoc hxIcc
  have hminorant := lrLowVHeadMinorant_six_nonneg hvIoc hxIcc
  have hle := lrLowVHeadMinorant_le_coefficient hv ht
    (n := 6) (by norm_num) (by norm_num) hGlow
  norm_num at hle
  exact hminorant.trans hle

end CourtadeKumar
