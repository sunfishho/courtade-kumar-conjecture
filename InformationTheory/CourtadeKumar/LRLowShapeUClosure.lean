import InformationTheory.CourtadeKumar.LRLowShapeUL1Certificate
import InformationTheory.CourtadeKumar.LRLowShapeUWPolynomialBridge
import InformationTheory.CourtadeKumar.LRLowShapeUTailActual

/-! Closure of every positive-index coefficient in the low-shape `U`
certificate. -/

open Set

namespace CourtadeKumar

theorem lrLowSecondScalar_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowH (v ^ 2 * t ^ 2) n *
          lrLowR v (t ^ 2) (lrGShape t v) n +
        2 * (n : ℝ) * (lrFlowBeta v + lrL (v * t)) *
          lrLowEta v (t ^ 2) n := by
  by_cases htail : 6 ≤ n
  · exact lrLowSecondScalar_tail_nonneg hv ht htSq htail
  · have hnle : n ≤ 5 := by omega
    interval_cases n
    · simpa using lrLowSecondScalar_one_nonneg hv ht htSq
    · simpa using lrLowSecondScalar_two_nonneg hv ht htSq
    · simpa using lrLowSecondScalar_three_nonneg hv ht htSq
    · simpa using lrLowSecondScalar_four_nonneg hv ht htSq
    · simpa using lrLowSecondScalar_five_nonneg hv ht htSq

theorem lrLowU_actual_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htSq : t ^ 2 ≤ (17 / 20 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lrLowUSignExplicit (lrFlowBeta v) (v ^ 2 * t ^ 2)
      (lrLowEta v (t ^ 2))
      (lrLowR v (t ^ 2) (lrGShape t v)) n := by
  have hfirst : 0 ≤
      lrLowR v (t ^ 2) (lrGShape t v) n +
        2 * lrFlowBeta v * lrLowEta v (t ^ 2) n := by
    have h := lrLowLambda_actual_nonneg hv
      (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩) htSq hn
    simpa [lrLowLambda] using h
  exact lrLowU_actual_nonneg_of_two_scalars hv ht n hfirst
    (lrLowSecondScalar_nonneg hv ht htSq hn)

end CourtadeKumar
