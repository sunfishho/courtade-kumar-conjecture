import InformationTheory.CourtadeKumar.LRCompactVWOneSeries

/-!
# Ratio-free grouped finite series for compact `V`

This file isolates the exact real identity behind the staged grouped leaf.
For a nonnegative scalar `lambda`, the finite expression retains the shared
shape variable in

`w * (T - h) + lambda * (1 - w) * (g - T)`

and pays the omitted `P_W` tail by `-h` times the omitted endpoint-kernel
weight.  The nonnegative constant term of `C` is deliberately omitted.

No choice of `lambda` is made here.  The checker-facing module can therefore
use the elementary independent ratio `D_lower / B_upper`, without proving a
monotonicity theorem for `D / B`.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The bilinear summand which preserves the two occurrences of `T`. -/
def lrCompactVLambdaGroup
    (lambda w T g h : ℝ) : ℝ :=
  w * (T - h) + lambda * (1 - w) * (g - T)

/-- The first `N` endpoint-kernel weights `a_n w_n(R)`. -/
noncomputable def lrCompactVWeightedScoreHead
    (N : ℕ) (R : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, lrCompactVWTerm R 1 (j + 1)

/-- The grouped finite head, without the known-nonnegative `f₀` term. -/
noncomputable def lrCompactVLambdaGroupedHead
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  let g := 4 / (1 + v)
  let h := 4 * lrCompactVMx v x
  ∑ j ∈ Finset.range N,
    lrLowA (j + 1) *
      lrCompactVLambdaGroup lambda
        (lrCompactVScore R (j + 1))
        (lrCompactVT v x (j + 1)) g h

/-- The exact finite minorant after paying the omitted `P_W` tail. -/
noncomputable def lrCompactVLambdaGroupedFinite
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  let h := 4 * lrCompactVMx v x
  lrCompactVLambdaGroupedHead N lambda R v x -
    h * (lrWKernel R 1 - lrCompactVWeightedScoreHead N R)

theorem lrCompactVWeightedScoreHead_le_lrWKernel
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    lrCompactVWeightedScoreHead N R ≤ lrWKernel R 1 := by
  have hseries := lrCompactVWOneTerm_hasSum hR
  rw [← hseries.tsum_eq]
  unfold lrCompactVWeightedScoreHead
  exact hseries.summable.sum_le_tsum (Finset.range N) (fun j _ ↦ by
    unfold lrCompactVWTerm
    exact mul_nonneg
      (mul_nonneg (lrLowA_pos (by omega)).le
        (lrCompactVScore_nonneg hR.1.le (by omega)))
      (pow_nonneg zero_le_one _))

theorem lrCompactVLambdaGroupedTerm_identity
    (lambda R v x : ℝ) (n : ℕ) :
    lrLowA n *
        lrCompactVLambdaGroup lambda
          (lrCompactVScore R n) (lrCompactVT v x n)
          (4 / (1 + v)) (4 * lrCompactVMx v x) =
      lrCompactVPWTerm R v x n -
        (4 * lrCompactVMx v x) * lrCompactVWTerm R 1 n +
        lambda * lrCompactVPsiTerm R v x n := by
  unfold lrCompactVLambdaGroup lrCompactVPWTerm lrCompactVWTerm
    lrCompactVPsiTerm lrCompactVC
  norm_num only [one_pow]
  ring

theorem lrCompactVLambdaGroupedHead_identity
    (N : ℕ) (lambda R v x : ℝ) :
    lrCompactVLambdaGroupedHead N lambda R v x =
      lrCompactVPWHead N R v x -
        (4 * lrCompactVMx v x) * lrCompactVWeightedScoreHead N R +
        lambda *
          ∑ j ∈ Finset.range N,
            lrCompactVPsiTerm R v x (j + 1) := by
  unfold lrCompactVLambdaGroupedHead lrCompactVPWHead
    lrCompactVWeightedScoreHead
  dsimp only
  simp_rw [lrCompactVLambdaGroupedTerm_identity]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

theorem lrCompactVLambdaGroupedFinite_identity
    (N : ℕ) (lambda R v x : ℝ) :
    lrCompactVLambdaGroupedFinite N lambda R v x =
      lrCompactVPWHead N R v x -
        4 * lrCompactVMx v x * lrWKernel R 1 +
        lambda *
          ∑ j ∈ Finset.range N,
            lrCompactVPsiTerm R v x (j + 1) := by
  rw [lrCompactVLambdaGroupedFinite,
    lrCompactVLambdaGroupedHead_identity]
  ring

theorem lrCompactVPsiTermHead_le_lrFlowC
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (N : ℕ) :
    (∑ j ∈ Finset.range N,
        lrCompactVPsiTerm R v (t ^ 2) (j + 1)) ≤
      lrFlowC R v t := by
  have hhead := lrCompactVPsiHead_le_lrFlowC hR hv ht N
  have hf0 := lrCompactVFZero_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
  unfold lrCompactVPsiHead at hhead
  linarith

/-- The finite grouped expression is a lower bound for `Q + lambda C`.
The omitted constant term and both omitted positive series tails are handled
analytically, so the later interval checker needs no extra transcendental
payload. -/
theorem lrCompactVLambdaGroupedFinite_le
    {R v t lambda : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hlambda : 0 ≤ lambda) (N : ℕ) :
    lrCompactVLambdaGroupedFinite N lambda R v (t ^ 2) ≤
      (lrFlowPW R v t -
        4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v))) +
        lambda * lrFlowC R v t := by
  have hPW := lrCompactVPWHead_le_lrFlowPW hR hv ht N
  have hPsi := lrCompactVPsiTermHead_le_lrFlowC hR hv ht N
  have hLambdaPsi := mul_le_mul_of_nonneg_left hPsi hlambda
  rw [lrCompactVLambdaGroupedFinite_identity]
  unfold lrCompactVMx
  linarith

end CourtadeKumar
