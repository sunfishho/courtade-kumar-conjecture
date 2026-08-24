import InformationTheory.CourtadeKumar.LoewnerScalar

/-! The explicit two-by-two positive-semidefinite Loewner certificate. -/

open Set

namespace CourtadeKumar

noncomputable def loewnerV (p tau : ℝ) : ℝ := p ^ 2 * tau

noncomputable def loewnerW (p : ℝ) : ℝ := 1 - 2 * p

noncomputable def loewnerB11 (p tau u : ℝ) : ℝ :=
  u ^ 2 * loewnerLeadingReserve p tau

noncomputable def loewnerB12 (p tau u : ℝ) : ℝ :=
  -u * loewnerW p * (1 + loewnerV p tau * loewnerR p tau)

noncomputable def loewnerB22 (p tau : ℝ) : ℝ :=
  loewnerZ p tau + loewnerV p tau * loewnerLeadingReserve p tau

noncomputable def loewnerBDet (p tau u : ℝ) : ℝ :=
  loewnerB11 p tau u * loewnerB22 p tau - loewnerB12 p tau u ^ 2

noncomputable def loewnerBMatrix (p tau u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![loewnerB11 p tau u, loewnerB12 p tau u;
    loewnerB12 p tau u, loewnerB22 p tau]

theorem loewnerZ_pos
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerZ p tau := by
  have hnonneg : 0 ≤ 1 + tau := by linarith [htau.1]
  have hle : p * (1 + tau) ≤ (1 / 2 : ℝ) * (1 + tau) :=
    mul_le_mul_of_nonneg_right hp.2 hnonneg
  have hlast : 0 < 1 - p * (1 + tau) := by
    nlinarith [hle, htau.2]
  rw [show loewnerZ p tau = p * (1 - p * (1 + tau)) by
    unfold loewnerZ
    ring]
  exact mul_pos hp.1 hlast

theorem loewnerB11_nonneg
    {p tau u : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ loewnerB11 p tau u := by
  unfold loewnerB11
  exact mul_nonneg (sq_nonneg u) (loewnerLeadingReserve_nonneg hp htau)

theorem loewnerB22_pos
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerB22 p tau := by
  unfold loewnerB22 loewnerV
  exact add_pos_of_pos_of_nonneg
    (loewnerZ_pos hp htau)
    (mul_nonneg (mul_nonneg (sq_nonneg p) htau.1)
      (loewnerLeadingReserve_nonneg hp htau))

/-- Equation (14): the matrix determinant is a positive factor times the scalar reserve. -/
theorem loewnerBDet_eq
    {p tau u : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    loewnerBDet p tau u =
      (u ^ 2 * p / (loewnerY p tau * loewnerEll p tau ^ 2)) *
        loewnerDetReserve p tau := by
  have hX := loewnerX_pos hp htau
  have hY := (loewnerY_mem_Ioo hp htau).1
  have hellLower := loewnerEll_ge_two_mul hp htau
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le hellLower
  unfold loewnerBDet loewnerB11 loewnerB12 loewnerB22
    loewnerLeadingReserve loewnerV loewnerW loewnerR
  field_simp [hX.ne', hY.ne', hell.ne']
  unfold loewnerDetReserve loewnerEll
  unfold loewnerX loewnerY loewnerZ
  ring

theorem loewnerBDet_nonneg
    {p tau u : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ loewnerBDet p tau u := by
  rw [loewnerBDet_eq hp htau]
  have hfactor : 0 ≤
      u ^ 2 * p / (loewnerY p tau * loewnerEll p tau ^ 2) :=
    div_nonneg
      (mul_nonneg (sq_nonneg u) hp.1.le)
      (mul_nonneg (loewnerY_mem_Ioo hp htau).1.le
        (sq_nonneg (loewnerEll p tau)))
  exact mul_nonneg hfactor (loewnerDetReserve_nonneg hp htau)

theorem loewnerBDet_pos
    {p tau u : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (hu : u ≠ 0) :
    0 < loewnerBDet p tau u := by
  rw [loewnerBDet_eq ⟨hp.1, hp.2.le⟩ htau]
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le
      (loewnerEll_ge_two_mul ⟨hp.1, hp.2.le⟩ htau)
  have hfactor : 0 <
      u ^ 2 * p / (loewnerY p tau * loewnerEll p tau ^ 2) :=
    div_pos
      (mul_pos (sq_pos_of_ne_zero hu) hp.1)
      (mul_pos (loewnerY_mem_Ioo ⟨hp.1, hp.2.le⟩ htau).1
        (sq_pos_of_pos hell))
  exact mul_pos hfactor (loewnerDetReserve_pos hp htau)

/-- The elementary scalar criterion for a symmetric two-by-two quadratic form. -/
theorem two_by_two_quadratic_nonneg
    {a b c x y : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : 0 ≤ a * c - b ^ 2) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rcases ha.eq_or_lt with rfl | ha
  · have hb : b = 0 := by nlinarith [sq_nonneg b]
    simp [hb, mul_nonneg hc (sq_nonneg y)]
  · have hid : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) =
        (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by
      ring
    have hrhs : 0 ≤ (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg y))
    nlinarith

theorem two_by_two_quadratic_pos
    {a b c x y : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : 0 < a * c - b ^ 2)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have ha' : 0 < a := by
    refine lt_of_le_of_ne ha ?_
    intro ha0
    rw [ha0] at hdet
    nlinarith [sq_nonneg b]
  have hid : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) =
      (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by
    ring
  have hrhs : 0 < (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by
    by_cases hy : y = 0
    · subst y
      have hs := sq_pos_of_ne_zero
        (mul_ne_zero ha'.ne' (hxy.resolve_right (by simp)))
      norm_num at ⊢
      exact hs
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hdet (sq_pos_of_ne_zero hy))
  rw [← hid] at hrhs
  exact ((mul_pos_iff.mp hrhs).resolve_right (by
    intro hneg
    linarith [hneg.1])).2

/-- The inner matrix in the differentiated Loewner quotient is positive semidefinite. -/
theorem loewnerB_quadratic_nonneg
    {p tau u x y : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 ≤ loewnerB11 p tau u * x ^ 2 +
      2 * loewnerB12 p tau u * x * y + loewnerB22 p tau * y ^ 2 := by
  exact two_by_two_quadratic_nonneg
    (loewnerB11_nonneg hp htau)
    (loewnerB22_pos hp htau).le
    (loewnerBDet_nonneg hp htau)

/-- Matrix-form version of the explicit Loewner certificate. -/
theorem loewnerBMatrix_posSemidef
    {p tau u : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    Matrix.PosSemidef (loewnerBMatrix p tau u) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [loewnerBMatrix]
  · intro x
    have hq := loewnerB_quadratic_nonneg (p := p) (tau := tau) (u := u)
      (x := x 0) (y := x 1) hp htau
    simp [loewnerBMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_add]
    nlinarith

/-- Strict form away from the centered boundary and the degenerate direction `u = 0`. -/
theorem loewnerBMatrix_posDef
    {p tau u : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (hu : u ≠ 0) :
    Matrix.PosDef (loewnerBMatrix p tau u) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [loewnerBMatrix]
  · intro x hx
    have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      funext i
      fin_cases i <;> simp [h]
    have hq := two_by_two_quadratic_pos
      (loewnerB11_nonneg ⟨hp.1, hp.2.le⟩ htau)
      (loewnerB22_pos ⟨hp.1, hp.2.le⟩ htau).le
      (loewnerBDet_pos hp htau hu) hcoords
    simp [loewnerBMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_add]
    nlinarith

end CourtadeKumar
