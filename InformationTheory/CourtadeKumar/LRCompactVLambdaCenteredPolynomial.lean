import InformationTheory.CourtadeKumar.LRCompactVLambdaPositiveGroupedCore

/-!
# Polynomialized positive grouped finite expression

Multiplying the positive grouped finite minorant by `1+v` removes its only
`v`-denominators.  With

`U_n(v) = (1+v)(1+v^(2n-1))`

and

`A_n(lambda,R) = (1+lambda) w_n(R) - lambda`,

the resulting expression is the finite polynomial

`sum a_n [A_n x^n U_n + 4 lambda (1-w_n)] - 4 v x W_R(1)`.

The identity in this module is purely algebraic.  It is the real-valued
bridge that later interval and derivative checkers will target.
-/

set_option autoImplicit false

open scoped BigOperators

namespace CourtadeKumar

/-- The polynomial shape factor obtained from `(1+v) * T_n`. -/
def lrCompactVCenteredU (v : ℝ) (n : ℕ) : ℝ :=
  (1 + v) * (1 + v ^ (2 * n - 1))

/-- Coefficient of `x^n U_n` in the polynomialized positive group. -/
def lrCompactVLambdaCenteredA
    (lambda R : ℝ) (n : ℕ) : ℝ :=
  (1 + lambda) * lrCompactVScore R n - lambda

/-- One term of the polynomialized positive grouped head. -/
noncomputable def lrCompactVLambdaCenteredPolynomialTerm
    (lambda R v x : ℝ) (n : ℕ) : ℝ :=
  lrLowA n *
    (lrCompactVLambdaCenteredA lambda R n * x ^ n *
        lrCompactVCenteredU v n +
      4 * lambda * (1 - lrCompactVScore R n))

/-- First `N` terms of the polynomialized positive grouped head. -/
noncomputable def lrCompactVLambdaCenteredPolynomialHead
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lrCompactVLambdaCenteredPolynomialTerm
      lambda R v x (j + 1)

/-- Polynomialized positive grouped finite expression, including the full
endpoint-kernel payment. -/
noncomputable def lrCompactVLambdaCenteredPolynomialFinite
    (N : ℕ) (lambda R v x : ℝ) : ℝ :=
  lrCompactVLambdaCenteredPolynomialHead N lambda R v x -
    4 * v * x * lrWKernel R 1

/-- Termwise polynomialization after clearing the positive-group
denominator. -/
theorem lrCompactVLambdaPositiveGroup_mul_one_add
    {v : ℝ} (hv : 1 + v ≠ 0) (lambda R x : ℝ) (n : ℕ) :
    (1 + v) *
        (lrLowA n *
          lrCompactVLambdaPositiveGroup lambda
            (lrCompactVScore R n) (lrCompactVT v x n)
            (4 / (1 + v))) =
      lrCompactVLambdaCenteredPolynomialTerm lambda R v x n := by
  unfold lrCompactVLambdaPositiveGroup
    lrCompactVLambdaCenteredPolynomialTerm
    lrCompactVLambdaCenteredA lrCompactVCenteredU lrCompactVT
  field_simp [hv]
  ring

/-- The positive grouped head becomes the displayed polynomial head after
multiplication by `1+v`. -/
theorem lrCompactVLambdaPositiveGroupedHead_mul_one_add
    {v : ℝ} (hv : 1 + v ≠ 0)
    (N : ℕ) (lambda R x : ℝ) :
    (1 + v) * lrCompactVLambdaPositiveGroupedHead N lambda R v x =
      lrCompactVLambdaCenteredPolynomialHead N lambda R v x := by
  unfold lrCompactVLambdaPositiveGroupedHead
    lrCompactVLambdaCenteredPolynomialHead
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact lrCompactVLambdaPositiveGroup_mul_one_add
    hv lambda R x (j + 1)

/-- Exact real identity used by the centered-Taylor leaf. -/
theorem lrCompactVLambdaPositiveGroupedFinite_mul_one_add
    {v : ℝ} (hv : 1 + v ≠ 0)
    (N : ℕ) (lambda R x : ℝ) :
    (1 + v) *
        lrCompactVLambdaPositiveGroupedFinite N lambda R v x =
      lrCompactVLambdaCenteredPolynomialFinite N lambda R v x := by
  rw [lrCompactVLambdaPositiveGroupedFinite,
    mul_sub, lrCompactVLambdaPositiveGroupedHead_mul_one_add hv]
  unfold lrCompactVLambdaCenteredPolynomialFinite lrCompactVMx
  field_simp [hv]

end CourtadeKumar
