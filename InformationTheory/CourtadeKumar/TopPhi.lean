import InformationTheory.CourtadeKumar.TopEntropyScalarCore
import Mathlib.Tactic.Linarith

/-! Convexity and endpoint bounds for the natural entropy deficiency `Phi`. -/

open Set
open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

@[simp] lemma topPhi_neg (x : ℝ) : topPhi (-x) = topPhi x := by
  unfold topPhi
  rw [show (1 - -x) / 2 = 1 - (1 - x) / 2 by ring,
    Real.binEntropy_one_sub]

lemma biasToProbability_mem_Icc {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (1 - x) / 2 ∈ Icc (0 : ℝ) 1 := by
  constructor <;> linarith [hx.1, hx.2]

/-- The entropy deficiency `Phi` is convex on the full bias interval. -/
theorem topPhi_convexOn : ConvexOn ℝ (Icc (-1 : ℝ) 1) topPhi := by
  constructor
  · exact convex_Icc (-1) 1
  · intro x hx y hy a b ha hb hab
    have hx' := biasToProbability_mem_Icc hx
    have hy' := biasToProbability_mem_Icc hy
    have hEntropy := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
    have harg :
        (1 - (a * x + b * y)) / 2 =
          a * ((1 - x) / 2) + b * ((1 - y) / 2) := by
      nlinarith
    simp only [smul_eq_mul] at hEntropy ⊢
    unfold topPhi
    rw [harg]
    calc
      Real.log 2 - Real.binEntropy
          (a * ((1 - x) / 2) + b * ((1 - y) / 2)) ≤
          Real.log 2 -
            (a * Real.binEntropy ((1 - x) / 2) +
              b * Real.binEntropy ((1 - y) / 2)) :=
        sub_le_sub_left hEntropy _
      _ = a * (Real.log 2 - Real.binEntropy ((1 - x) / 2)) +
          b * (Real.log 2 - Real.binEntropy ((1 - y) / 2)) := by
            calc
              Real.log 2 -
                  (a * Real.binEntropy ((1 - x) / 2) +
                    b * Real.binEntropy ((1 - y) / 2)) =
                  (a + b) * Real.log 2 -
                    (a * Real.binEntropy ((1 - x) / 2) +
                      b * Real.binEntropy ((1 - y) / 2)) := by rw [hab]; ring
              _ = _ := by ring

lemma topPhi_nonneg {x : ℝ} (_hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ topPhi x := by
  unfold topPhi
  exact sub_nonneg.mpr Real.binEntropy_le_log_two

lemma topPhi_le_log_two {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    topPhi x ≤ Real.log 2 := by
  unfold topPhi
  have hprob := biasToProbability_mem_Icc hx
  exact sub_le_self _ (Real.binEntropy_nonneg hprob.1 hprob.2)

end CourtadeKumar
