import InformationTheory.CourtadeKumar.LRAbelCoefficients
import InformationTheory.CourtadeKumar.BernsteinCertificate

/-! The exact tensor Bernstein certificate used in the audited `B` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrBComparisonPolynomial (R v X : ℝ) : ℝ :=
  -R * v ^ 5 * X ^ 3 + 2 * R * v ^ 3 * X ^ 2 + R * v ^ 3 * X -
    R * v ^ 2 * X ^ 3 + 3 * R * v ^ 2 * X ^ 2 - 3 * R * v ^ 2 * X -
    R * X ^ 2 + v ^ 5 * X ^ 2 - 2 * v ^ 3 * X - v ^ 3 -
    2 * v ^ 2 * X + 3 * v ^ 2 + X ^ 2

def lrBComparisonCoeff0 (i : Fin 4) (j : Fin 6) : ℚ :=
  ![
    ![(0 : ℚ), 0, 3/10, 4/5, 7/5, 2],
    ![(0 : ℚ), 0, 7/30, 8/15, 11/15, 2/3],
    ![(1/3 : ℚ), 1/3, 1/2, 3/5, 2/5, 0],
    ![(1 : ℚ), 1, 11/10, 1, 2/5, 0]
  ] i j

def lrBComparisonCoeff1 (i : Fin 4) (j : Fin 6) : ℚ :=
  ![
    ![(0 : ℚ), 0, 3/10, 4/5, 7/5, 2],
    ![(0 : ℚ), 0, 2/15, 4/15, 4/15, 0],
    ![(0 : ℚ), 0, 1/15, 1/10, 0, 0],
    ![(0 : ℚ), 0, 0, 0, 0, 0]
  ] i j

noncomputable def lrBComparisonBernstein0 (v X : ℝ) : ℝ :=
  tensorBernsteinEval 3 5
    (fun i j ↦ (lrBComparisonCoeff0 i j : ℝ)) X v

noncomputable def lrBComparisonBernstein1 (v X : ℝ) : ℝ :=
  tensorBernsteinEval 3 5
    (fun i j ↦ (lrBComparisonCoeff1 i j : ℝ)) X v

noncomputable def lrBComparisonBernstein (R v X : ℝ) : ℝ :=
  (1 - R) * lrBComparisonBernstein0 v X +
    R * lrBComparisonBernstein1 v X

lemma lrBComparisonCoeff0_nonneg (i : Fin 4) (j : Fin 6) :
    0 ≤ lrBComparisonCoeff0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [lrBComparisonCoeff0]

lemma lrBComparisonCoeff1_nonneg (i : Fin 4) (j : Fin 6) :
    0 ≤ lrBComparisonCoeff1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [lrBComparisonCoeff1]

theorem lrBComparisonBernstein_nonneg
    {R v X : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hX : X ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrBComparisonBernstein R v X := by
  have h0 : 0 ≤ lrBComparisonBernstein0 v X := by
    apply tensorBernsteinEval_nonneg
    · intro i j
      exact_mod_cast lrBComparisonCoeff0_nonneg i j
    · exact hX
    · exact hv
  have h1 : 0 ≤ lrBComparisonBernstein1 v X := by
    apply tensorBernsteinEval_nonneg
    · intro i j
      exact_mod_cast lrBComparisonCoeff1_nonneg i j
    · exact hX
    · exact hv
  unfold lrBComparisonBernstein
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hR.2) h0)
    (mul_nonneg hR.1 h1)

lemma lrBComparisonBernstein0_eq (v X : ℝ) :
    lrBComparisonBernstein0 v X =
      v ^ 5 * X ^ 2 - 2 * v ^ 3 * X - v ^ 3 -
        2 * v ^ 2 * X + 3 * v ^ 2 + X ^ 2 := by
  unfold lrBComparisonBernstein0 tensorBernsteinEval bernsteinBasis
  simp [lrBComparisonCoeff0, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

lemma lrBComparisonBernstein1_eq (v X : ℝ) :
    lrBComparisonBernstein1 v X =
      -v ^ 5 * X ^ 3 + 2 * v ^ 3 * X ^ 2 + v ^ 3 * X -
        v ^ 2 * X ^ 3 + 3 * v ^ 2 * X ^ 2 - 3 * v ^ 2 * X -
        X ^ 2 + v ^ 5 * X ^ 2 - 2 * v ^ 3 * X - v ^ 3 -
        2 * v ^ 2 * X + 3 * v ^ 2 + X ^ 2 := by
  unfold lrBComparisonBernstein1 tensorBernsteinEval bernsteinBasis
  simp [lrBComparisonCoeff1, Fin.sum_univ_succ]
  norm_num [Nat.choose]
  ring

theorem lrBComparisonPolynomial_eq_bernstein (R v X : ℝ) :
    lrBComparisonPolynomial R v X = lrBComparisonBernstein R v X := by
  rw [lrBComparisonBernstein, lrBComparisonBernstein0_eq,
    lrBComparisonBernstein1_eq]
  unfold lrBComparisonPolynomial
  ring

theorem lrBComparisonPolynomial_nonneg
    {R v X : ℝ} (hR : R ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hX : X ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrBComparisonPolynomial R v X := by
  rw [lrBComparisonPolynomial_eq_bernstein]
  exact lrBComparisonBernstein_nonneg hR hv hX

end CourtadeKumar
