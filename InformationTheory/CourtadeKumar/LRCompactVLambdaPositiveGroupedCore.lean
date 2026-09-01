import InformationTheory.CourtadeKumar.LRCompactVLambdaGroupedCore

/-!
# Positive-head reformulation of the compact `V` grouped series

The original grouped summand keeps the endpoint-tail payment inside each
term.  Adding that payment back produces the manifestly positive expression

`w * T + lambda * (1 - w) * (g - T)`.

The corresponding finite expression subtracts the complete endpoint kernel
`h * W_R(1)` only once.  The identities below show that this is exactly the
same real quantity as `lrCompactVLambdaGroupedFinite`, so the existing
analytic lower-bound theorem applies unchanged.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The grouped summand before paying the endpoint-kernel contribution. -/
def lrCompactVLambdaPositiveGroup
    (lambda w T g : ℝ) : ℝ :=
  w * T + lambda * (1 - w) * (g - T)

/-- Positivity of the reformulated grouped summand. -/
theorem lrCompactVLambdaPositiveGroup_nonneg
    {lambda w T g : ℝ}
    (hlambda : 0 ≤ lambda) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hT0 : 0 ≤ T) (hTg : T ≤ g) :
    0 ≤ lrCompactVLambdaPositiveGroup lambda w T g := by
  unfold lrCompactVLambdaPositiveGroup
  exact add_nonneg (mul_nonneg hw0 hT0)
    (mul_nonneg (mul_nonneg hlambda (sub_nonneg.mpr hw1))
      (sub_nonneg.mpr hTg))

/-- Every positive-head series term is nonnegative under the elementary
shape bounds. -/
theorem lrCompactVLambdaPositiveGroupedTerm_nonneg
    {lambda w T g : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hlambda : 0 ≤ lambda) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hT0 : 0 ≤ T) (hTg : T ≤ g) :
    0 ≤ lrLowA n * lrCompactVLambdaPositiveGroup lambda w T g := by
  exact mul_nonneg (lrLowA_pos hn).le
    (lrCompactVLambdaPositiveGroup_nonneg hlambda hw0 hw1 hT0 hTg)

/-- The first `N` terms of the manifestly positive grouped series. -/
noncomputable def lrCompactVLambdaPositiveGroupedHead
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  let g := 4 / (1 + v)
  ∑ j ∈ Finset.range N,
    lrLowA (j + 1) *
      lrCompactVLambdaPositiveGroup lambda
        (lrCompactVScore R (j + 1))
        (lrCompactVT v x (j + 1)) g

/-- The positive head after paying the complete endpoint-kernel term. -/
noncomputable def lrCompactVLambdaPositiveGroupedFinite
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  let h := 4 * lrCompactVMx v x
  lrCompactVLambdaPositiveGroupedHead N lambda R v x -
    h * lrWKernel R 1

/-- Adding the endpoint payment back to one grouped summand produces the
positive summand. -/
theorem lrCompactVLambdaPositiveGroupedTerm_eq
    (lambda R v x : ℝ) (n : ℕ) :
    lrLowA n *
        lrCompactVLambdaPositiveGroup lambda
          (lrCompactVScore R n) (lrCompactVT v x n)
          (4 / (1 + v)) =
      lrLowA n *
          lrCompactVLambdaGroup lambda
            (lrCompactVScore R n) (lrCompactVT v x n)
            (4 / (1 + v)) (4 * lrCompactVMx v x) +
        (4 * lrCompactVMx v x) * lrCompactVWTerm R 1 n := by
  unfold lrCompactVLambdaPositiveGroup lrCompactVLambdaGroup lrCompactVWTerm
  norm_num only [one_pow]
  ring

/-- The positive head is the old grouped head plus the truncated endpoint
score series. -/
theorem lrCompactVLambdaPositiveGroupedHead_eq
    (N : ℕ) (lambda R v x : ℝ) :
    lrCompactVLambdaPositiveGroupedHead N lambda R v x =
      lrCompactVLambdaGroupedHead N lambda R v x +
        (4 * lrCompactVMx v x) * lrCompactVWeightedScoreHead N R := by
  unfold lrCompactVLambdaPositiveGroupedHead
    lrCompactVLambdaGroupedHead lrCompactVWeightedScoreHead
  dsimp only
  simp_rw [lrCompactVLambdaPositiveGroupedTerm_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Paying the complete endpoint kernel after the positive head gives
exactly the existing grouped finite minorant. -/
theorem lrCompactVLambdaPositiveGroupedFinite_eq
    (N : ℕ) (lambda R v x : ℝ) :
    lrCompactVLambdaPositiveGroupedFinite N lambda R v x =
      lrCompactVLambdaGroupedFinite N lambda R v x := by
  rw [lrCompactVLambdaPositiveGroupedFinite,
    lrCompactVLambdaPositiveGroupedHead_eq,
    lrCompactVLambdaGroupedFinite]
  ring

/-- The existing analytic lower bound, stated for the positive-head form. -/
theorem lrCompactVLambdaPositiveGroupedFinite_le
    {R v t lambda : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hlambda : 0 ≤ lambda) (N : ℕ) :
    lrCompactVLambdaPositiveGroupedFinite N lambda R v (t ^ 2) ≤
      (lrFlowPW R v t -
        4 * lrWKernel R 1 * (v * t ^ 2 / (1 + v))) +
        lambda * lrFlowC R v t := by
  rw [lrCompactVLambdaPositiveGroupedFinite_eq]
  exact lrCompactVLambdaGroupedFinite_le hR hv ht hlambda N

end CourtadeKumar
