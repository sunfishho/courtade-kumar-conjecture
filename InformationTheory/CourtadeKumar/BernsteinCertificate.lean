import InformationTheory.CourtadeKumar.CapClosure
import Mathlib.RingTheory.Polynomial.Bernstein

/-! Reusable positivity infrastructure for the exact tensor Bernstein
certificates in the corrected TOP argument. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

/-- The normalized Bernstein basis function of degree `n` and index `i`. -/
def bernsteinBasis (n i : ℕ) (x : ℝ) : ℝ :=
  (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)

lemma bernsteinBasis_nonneg {n i : ℕ} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ bernsteinBasis n i x := by
  unfold bernsteinBasis
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

/-- Evaluation of a coefficient table in the normalized tensor Bernstein
basis.  The finite index types make a concrete rational certificate directly
computable by Lean. -/
def tensorBernsteinEval (m n : ℕ)
    (p : Fin (m + 1) → Fin (n + 1) → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, p i j * bernsteinBasis m i x * bernsteinBasis n j y

/-- A tensor Bernstein table with nonnegative coefficients is nonnegative on
the closed unit square. -/
theorem tensorBernsteinEval_nonneg
    {m n : ℕ} {p : Fin (m + 1) → Fin (n + 1) → ℝ} {x y : ℝ}
    (hp : ∀ i j, 0 ≤ p i j)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ tensorBernsteinEval m n p x y := by
  unfold tensorBernsteinEval
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (hp i j) (bernsteinBasis_nonneg hx))
    (bernsteinBasis_nonneg hy)

/-- If a function agrees with a nonnegative tensor Bernstein expansion on the
unit square, it is nonnegative there. -/
theorem nonneg_of_eq_tensorBernsteinEval
    {m n : ℕ} {p : Fin (m + 1) → Fin (n + 1) → ℝ} {f : ℝ → ℝ → ℝ}
    (hp : ∀ i j, 0 ≤ p i j)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      f x y = tensorBernsteinEval m n p x y)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ f x y := by
  rw [heq x hx y hy]
  exact tensorBernsteinEval_nonneg hp hx hy

end CourtadeKumar
