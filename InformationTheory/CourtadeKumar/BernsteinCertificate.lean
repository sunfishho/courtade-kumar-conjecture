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

/-- Power-basis expansion of one normalized Bernstein basis function.  The
shifted index avoids any division by binomial coefficients. -/
lemma bernsteinBasis_eq_sum_shiftedPower (n i : ℕ) (x : ℝ) :
    bernsteinBasis n i x =
      ∑ k ∈ Finset.range (n - i + 1),
        ((n.choose i : ℝ) * (n - i).choose k * (-1 : ℝ) ^ k) *
          x ^ (i + k) := by
  rw [bernsteinBasis, sub_eq_add_neg,
    show (1 : ℝ) + -x = -x + 1 by ring, add_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow]
  rw [neg_pow, pow_add]
  ring

/-- The explicit fourfold power expansion of a tensor Bernstein table. -/
def tensorBernsteinPowerExpansion (m n : ℕ)
    (p : Fin (m + 1) → Fin (n + 1) → ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j,
    ∑ l ∈ Finset.range (n - j.val + 1),
      ∑ k ∈ Finset.range (m - i.val + 1),
        p i j *
          ((m.choose i.val : ℝ) * (m - i.val).choose k * (-1 : ℝ) ^ k) *
          ((n.choose j.val : ℝ) * (n - j.val).choose l * (-1 : ℝ) ^ l) *
          x ^ (i.val + k) * y ^ (j.val + l)

theorem tensorBernsteinEval_eq_powerExpansion
    (m n : ℕ) (p : Fin (m + 1) → Fin (n + 1) → ℝ) (x y : ℝ) :
    tensorBernsteinEval m n p x y =
      tensorBernsteinPowerExpansion m n p x y := by
  classical
  unfold tensorBernsteinEval tensorBernsteinPowerExpansion
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [bernsteinBasis_eq_sum_shiftedPower,
    bernsteinBasis_eq_sum_shiftedPower]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Reindex the triangular set `(i,k)` by total degree `a = i+k`. -/
lemma sum_range_triangle_shift
    {M : Type} [AddCommMonoid M] (m : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (m - i + 1), f i (i + k)) =
    ∑ a ∈ Finset.range (m + 1),
      ∑ i ∈ Finset.range (a + 1), f i a := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun ik _ ↦ ⟨ik.1 + ik.2, ik.1⟩)
  · simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · rintro ⟨i, k⟩ hi ⟨i', k'⟩ hi' hxy
    simp only [Sigma.mk.inj_iff] at hxy
    have hii : i = i' := eq_of_heq hxy.2
    subst i'
    have hkk : k = k' := Nat.add_left_cancel hxy.1
    subst k'
    rfl
  · simp only [Finset.mem_sigma, Finset.mem_range]
    rintro ⟨a, i⟩ ⟨ha, hi⟩
    change a < m + 1 at ha
    change i < a + 1 at hi
    have hai : i ≤ a := by omega
    have ham : a ≤ m := by omega
    refine ⟨⟨i, a - i⟩, ?_, ?_⟩
    · change i < m + 1 ∧ a - i < m - i + 1
      omega
    apply Sigma.ext
    · exact Nat.add_sub_of_le hai
    · simp
  · simp only [Finset.mem_sigma, Finset.mem_range]
    rintro ⟨i, k⟩ hik
    trivial

/-- Bivariate triangular reindexing used to group a tensor Bernstein
expansion by its two power-basis exponents. -/
lemma sum_range_triangle4
    {M : Type} [AddCommMonoid M] (m n : ℕ)
    (f : ℕ → ℕ → ℕ → ℕ → M) :
    (∑ i ∈ Finset.range (m + 1),
      ∑ j ∈ Finset.range (n + 1),
        ∑ l ∈ Finset.range (n - j + 1),
          ∑ k ∈ Finset.range (m - i + 1), f i j k l) =
    ∑ a ∈ Finset.range (m + 1),
      ∑ b ∈ Finset.range (n + 1),
        ∑ i ∈ Finset.range (a + 1),
          ∑ j ∈ Finset.range (b + 1), f i j (a - i) (b - j) := by
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (m + 1),
            ∑ l ∈ Finset.range (n - j + 1),
              ∑ k ∈ Finset.range (m - i + 1), f i j k l := by
        rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (m - i + 1),
              ∑ l ∈ Finset.range (n - j + 1), f i j k l := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (n + 1),
          ∑ a ∈ Finset.range (m + 1),
            ∑ i ∈ Finset.range (a + 1),
              ∑ l ∈ Finset.range (n - j + 1), f i j (a - i) l := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Nat.add_sub_cancel_left] using
          sum_range_triangle_shift m
            (fun i a ↦ ∑ l ∈ Finset.range (n - j + 1), f i j (a - i) l)
    _ = ∑ a ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (n + 1),
            ∑ i ∈ Finset.range (a + 1),
              ∑ l ∈ Finset.range (n - j + 1), f i j (a - i) l := by
        rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (n + 1),
            ∑ l ∈ Finset.range (n - j + 1),
              ∑ i ∈ Finset.range (a + 1), f i j (a - i) l := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.range (m + 1),
          ∑ b ∈ Finset.range (n + 1),
            ∑ j ∈ Finset.range (b + 1),
              ∑ i ∈ Finset.range (a + 1), f i j (a - i) (b - j) := by
        apply Finset.sum_congr rfl
        intro a ha
        simpa only [Nat.add_sub_cancel_left] using
          sum_range_triangle_shift n
            (fun j b ↦ ∑ i ∈ Finset.range (a + 1), f i j (a - i) (b - j))
    _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_comm]

/-- Read a finite coefficient table using natural-number indices, returning
zero outside its declared rectangle. -/
def finTableGet {R : Type} [Zero R] {m n : ℕ}
    (p : Fin (m + 1) → Fin (n + 1) → R) (i j : ℕ) : R :=
  if hi : i < m + 1 then
    if hj : j < n + 1 then p ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- Contribution of one Bernstein coefficient to one shifted pair of power
exponents. -/
def tensorBernsteinPowerSummand {R : Type} [CommRing R] {m n : ℕ}
    (p : Fin (m + 1) → Fin (n + 1) → R) (i j k l : ℕ) : R :=
  finTableGet p i j *
    ((m.choose i : R) * (m - i).choose k * (-1 : R) ^ k) *
    ((n.choose j : R) * (n - j).choose l * (-1 : R) ^ l)

/-- Power-basis coefficient obtained from a tensor Bernstein table. -/
def tensorBernsteinPowerCoeff {R : Type} [CommRing R] {m n : ℕ}
    (p : Fin (m + 1) → Fin (n + 1) → R) (a b : ℕ) : R :=
  ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
    tensorBernsteinPowerSummand p i j (a - i) (b - j)

def tensorBernsteinPowerEval {R : Type} [CommRing R] (m n : ℕ)
    (p : Fin (m + 1) → Fin (n + 1) → R) (x y : R) : R :=
  ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (n + 1),
    tensorBernsteinPowerCoeff p a b * x ^ a * y ^ b

/-- Group the fourfold shifted expansion by its two resulting power
exponents. -/
theorem tensorBernsteinPowerExpansion_eq_powerEval
    (m n : ℕ) (p : Fin (m + 1) → Fin (n + 1) → ℝ) (x y : ℝ) :
    tensorBernsteinPowerExpansion m n p x y =
      tensorBernsteinPowerEval m n p x y := by
  classical
  unfold tensorBernsteinPowerExpansion tensorBernsteinPowerEval
  calc
    _ = ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
          ∑ l ∈ Finset.range (n - j.val + 1),
            ∑ k ∈ Finset.range (m - i.val + 1),
              tensorBernsteinPowerSummand p i.val j.val k l *
                x ^ (i.val + k) * y ^ (j.val + l) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        have him : i.val ≤ m := Nat.le_of_lt_succ i.isLt
        have hjn : j.val ≤ n := Nat.le_of_lt_succ j.isLt
        simp [tensorBernsteinPowerSummand, finTableGet, him, hjn]
    _ = ∑ i ∈ Finset.range (m + 1), ∑ j : Fin (n + 1),
          ∑ l ∈ Finset.range (n - j.val + 1),
            ∑ k ∈ Finset.range (m - i + 1),
              tensorBernsteinPowerSummand p i j.val k l *
                x ^ (i + k) * y ^ (j.val + l) := by
        exact Fin.sum_univ_eq_sum_range
          (fun i ↦ ∑ j : Fin (n + 1),
            ∑ l ∈ Finset.range (n - j.val + 1),
              ∑ k ∈ Finset.range (m - i + 1),
                tensorBernsteinPowerSummand p i j.val k l *
                  x ^ (i + k) * y ^ (j.val + l)) (m + 1)
    _ = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (n - j + 1),
            ∑ k ∈ Finset.range (m - i + 1),
              tensorBernsteinPowerSummand p i j k l *
                x ^ (i + k) * y ^ (j + l) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Fin.sum_univ_eq_sum_range
          (fun j ↦ ∑ l ∈ Finset.range (n - j + 1),
            ∑ k ∈ Finset.range (m - i + 1),
              tensorBernsteinPowerSummand p i j k l *
                x ^ (i + k) * y ^ (j + l)) (n + 1)
    _ = ∑ a ∈ Finset.range (m + 1),
          ∑ b ∈ Finset.range (n + 1),
            ∑ i ∈ Finset.range (a + 1),
              ∑ j ∈ Finset.range (b + 1),
                tensorBernsteinPowerSummand p i j (a - i) (b - j) *
                  x ^ a * y ^ b := by
        rw [sum_range_triangle4]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hia' : i < a + 1 := Finset.mem_range.mp hi
        have hjb' : j < b + 1 := Finset.mem_range.mp hj
        have hia : i ≤ a := by omega
        have hjb : j ≤ b := by omega
        rw [Nat.add_sub_of_le hia, Nat.add_sub_of_le hjb]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        unfold tensorBernsteinPowerCoeff
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul, Finset.sum_mul]

theorem tensorBernsteinEval_eq_powerEval
    (m n : ℕ) (p : Fin (m + 1) → Fin (n + 1) → ℝ) (x y : ℝ) :
    tensorBernsteinEval m n p x y = tensorBernsteinPowerEval m n p x y :=
  (tensorBernsteinEval_eq_powerExpansion m n p x y).trans
    (tensorBernsteinPowerExpansion_eq_powerEval m n p x y)

end CourtadeKumar
