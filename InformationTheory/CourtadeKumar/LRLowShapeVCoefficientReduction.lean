import InformationTheory.CourtadeKumar.LRLowShapeTClosure

/-!
# Scalar reduction of each positive-index low-shape `V` coefficient

This is the exact identity `V_(n-1) = L_n + n A p_n` from the supplied
tangent certificate.
-/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowCStar (n : ℕ) : ℝ :=
  4 * lrLowB n

noncomputable def lrLowDelta (v x : ℝ) : ℝ :=
  (1 - v * x) / (1 + v)

noncomputable def lrLowVComparisonConstant (v x : ℝ) : ℝ :=
  lrL (v * Real.sqrt x) / (1 + v) +
    lrFlowBeta v * lrFlowM v * x

noncomputable def lrLowVComparison
    (v x G : ℝ) (n : ℕ) : ℝ :=
  G *
      (((n : ℝ) * lrL (v * Real.sqrt x)) -
        (1 / 2 : ℝ) *
          ∑ k ∈ Finset.range (n - 1),
            ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
              (v ^ 2 * x) ^ (k + 1)) -
    (n : ℝ) * lrLowVComparisonConstant v x * lrLowCStar n +
    lrLowDelta v x / 2 *
      ∑ k ∈ Finset.range (n - 1),
        ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (v ^ 2 * x) ^ (k + 1) * lrLowCStar (n - (k + 1))

lemma lrLowV_inner_term
    {v t G : ℝ} {n k : ℕ} (hk : k < n - 1) :
    lrLowDFlowCoeff v t (k + 1) *
          lrLowFDerivCoeff v (t ^ 2) G (n - 1 - (k + 1)) +
        lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) (k + 1) *
          lrLowYTangentCoeff v (t ^ 2) (n - 1 - (k + 1)) =
      -(G / 2) *
          (((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
            (v ^ 2 * t ^ 2) ^ (k + 1)) +
        lrLowDelta v (t ^ 2) / 2 *
          (((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
            (v ^ 2 * t ^ 2) ^ (k + 1) * lrLowCStar (n - (k + 1))) := by
  have hindex : n - 1 - (k + 1) + 1 = n - (k + 1) := by omega
  unfold lrLowDFlowCoeff lrLowBFlowCoeff lrLowFDerivCoeff
    lrLowYTangentCoeff lrLowDelta lrLowCStar lrFlowM
  simp only [Nat.succ_ne_zero, if_false]
  rw [hindex]
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  field_simp [hkpos.ne']
  ring

theorem lrLowVConvolutionCoeff_pred_eq_comparison
    {v t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 2 ≤ n) :
    lrLowVConvolutionCoeff v t (n - 1) =
      lrLowVComparison v (t ^ 2) (lrGShape t v) n +
        (n : ℝ) * lrFlowA v t * lrLowP v (t ^ 2) n := by
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht
  have hnPred : n - 1 + 1 = n := by omega
  have hinner : ∀ k ∈ Finset.range (n - 1),
      lrLowDFlowCoeff v t (k + 1) *
            lrLowFDerivCoeff v (t ^ 2) (lrGShape t v)
              (n - 1 - (k + 1)) +
          lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) (k + 1) *
            lrLowYTangentCoeff v (t ^ 2) (n - 1 - (k + 1)) =
        -(lrGShape t v / 2) *
            (((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
              (v ^ 2 * t ^ 2) ^ (k + 1)) +
          lrLowDelta v (t ^ 2) / 2 *
            (((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
              (v ^ 2 * t ^ 2) ^ (k + 1) *
                lrLowCStar (n - (k + 1))) := by
    intro k hk
    simpa using lrLowV_inner_term
      (v := v) (t := t) (G := lrGShape t v)
      (n := n) (k := k) (Finset.mem_range.mp hk)
  unfold lrLowVConvolutionCoeff
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  let sD := ∑ k ∈ Finset.range (n - 1),
    lrLowDFlowCoeff v t (k + 1) *
      lrLowFDerivCoeff v (t ^ 2) (lrGShape t v) (n - 1 - (k + 1))
  let sB := ∑ k ∈ Finset.range (n - 1),
    lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) (k + 1) *
      lrLowYTangentCoeff v (t ^ 2) (n - 1 - (k + 1))
  let zD := lrLowDFlowCoeff v t 0 *
    lrLowFDerivCoeff v (t ^ 2) (lrGShape t v) (n - 1 - 0)
  let zB := lrLowBFlowCoeff (lrFlowBeta v) (v ^ 2 * t ^ 2) 0 *
    lrLowYTangentCoeff v (t ^ 2) (n - 1 - 0)
  change (sD + zD) + (sB + zB) = _
  rw [show (sD + zD) + (sB + zB) = (sD + sB) + (zD + zB) by ring]
  dsimp [sD, sB]
  rw [← Finset.sum_add_distrib]
  have hsum := Finset.sum_congr rfl hinner
  rw [hsum]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  dsimp [zD, zB]
  unfold lrLowVComparison lrLowVComparisonConstant
    lrLowDFlowCoeff lrLowBFlowCoeff lrLowFDerivCoeff
    lrLowYTangentCoeff lrLowCStar
  simp only [if_pos]
  rw [hsqrt]
  unfold lrFlowA lrFlowM
  have hnPred' : 1 + (n - 1) = n := by omega
  have hsumG :
      (∑ k ∈ Finset.range (n - 1),
        ((n - (1 + k) : ℕ) : ℝ) / ((1 + k : ℕ) : ℝ) *
          v ^ 2 * v ^ (k * 2) * t ^ 2 * t ^ (k * 2)) =
      (∑ k ∈ Finset.range (n - 1),
        v ^ 2 * v ^ (k * 2) * t ^ 2 * t ^ (k * 2) *
          ((n - (1 + k) : ℕ) : ℝ) / ((1 + k : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  ring_nf at hsumG
  ring_nf
  rw [hnPred', hsumG]
  ring

end CourtadeKumar
