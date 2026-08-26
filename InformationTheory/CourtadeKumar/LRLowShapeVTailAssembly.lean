import InformationTheory.CourtadeKumar.LRLowShapeVL7Certificate
import InformationTheory.CourtadeKumar.LRLowShapeVStarBridge

/-! Assembly of the concrete low-shape `V` comparison tail. -/

open Set

namespace CourtadeKumar

theorem lrLowVComparison_nonneg_tail_lowShape
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ 17 / 20) :
    ∀ n : ℕ, 7 ≤ n →
      0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) n := by
  have hvIoc : v ∈ Ioc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
  have hxIcc : t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) :=
    ⟨sq_nonneg t, htSq⟩
  have hxIoc : t ^ 2 ∈ Ioc (0 : ℝ) (17 / 20) :=
    ⟨sq_pos_of_pos ht.1, htSq⟩
  have hGlow : 0 ≤ lrLowGShapeLower v (t ^ 2) :=
    lrLowGShapeLower_nonneg hvIoc hxIcc
  have hG : 0 ≤ lrGShape t v :=
    hGlow.trans (lrLowGShapeLower_le hv ht)
  have hminorant : 0 ≤ lrLowVComparisonMinorant v (t ^ 2) 7 :=
    lrLowVComparisonMinorant_seven_nonneg hvIoc hxIcc
  have hseven : 0 ≤ lrLowVComparison v (t ^ 2) (lrGShape t v) 7 :=
    hminorant.trans (lrLowVComparisonMinorant_le hv ht (by norm_num) (by norm_num) hGlow)
  exact lrLowVComparison_nonneg_tail hvIoc hxIoc hG
    (lrLowVStar_nonneg_lowShape hv ht htSq) hseven

end CourtadeKumar
