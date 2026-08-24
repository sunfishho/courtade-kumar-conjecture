import InformationTheory.CourtadeKumar.LoewnerMatrix

/-! Entrywise derivative identity underlying the Loewner certificate. -/

open Set

namespace CourtadeKumar

noncomputable def loewnerSigmaX (p u sigma : ℝ) : ℝ :=
  p ^ 2 - sigma * u ^ 2

noncomputable def loewnerSigmaY (p u sigma : ℝ) : ℝ :=
  (1 - p) ^ 2 - sigma * u ^ 2

noncomputable def loewnerSigmaZ (p u sigma : ℝ) : ℝ :=
  p * (1 - p) - sigma * u ^ 2

noncomputable def loewnerSigmaEll (p u sigma : ℝ) : ℝ :=
  -Real.log (loewnerSigmaY p u sigma)

noncomputable def loewnerSigmaDelta (p u sigma : ℝ) : ℝ :=
  loewnerSigmaEll p u sigma / 2

noncomputable def loewnerNormalizedG11 (p u sigma : ℝ) : ℝ :=
  loewnerSigmaZ p u sigma /
    (loewnerSigmaX p u sigma * loewnerSigmaY p u sigma *
      loewnerSigmaDelta p u sigma)

noncomputable def loewnerNormalizedG12 (p u sigma : ℝ) : ℝ :=
  (-sigma * u * (1 - 2 * p)) /
    (loewnerSigmaX p u sigma * loewnerSigmaY p u sigma *
      loewnerSigmaDelta p u sigma)

noncomputable def loewnerNormalizedG22 (p u sigma : ℝ) : ℝ :=
  (sigma * loewnerSigmaZ p u sigma) /
    (loewnerSigmaX p u sigma * loewnerSigmaY p u sigma *
      loewnerSigmaDelta p u sigma)

noncomputable def loewnerNormalizedGMatrix
    (p u sigma : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![loewnerNormalizedG11 p u sigma, loewnerNormalizedG12 p u sigma;
    loewnerNormalizedG12 p u sigma, loewnerNormalizedG22 p u sigma]

noncomputable def loewnerDerivativeFactor (p tau : ℝ) : ℝ :=
  1 / (loewnerX p tau * loewnerY p tau * (loewnerEll p tau / 2))

noncomputable def loewnerDerivativeMatrix
    (p tau u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![loewnerDerivativeFactor p tau * loewnerB11 p tau u,
      loewnerDerivativeFactor p tau * loewnerB12 p tau u;
    loewnerDerivativeFactor p tau * loewnerB12 p tau u,
      loewnerDerivativeFactor p tau * loewnerB22 p tau]

noncomputable def loewnerNormalizedQuadratic
    (p u x y sigma : ℝ) : ℝ :=
  loewnerNormalizedG11 p u sigma * x ^ 2 +
    2 * loewnerNormalizedG12 p u sigma * x * y +
    loewnerNormalizedG22 p u sigma * y ^ 2

def MatrixLoewnerLE
    (A B : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Matrix.PosSemidef (B - A)

private theorem loewnerSigma_values
    {p u sigma tau : ℝ}
    (hp : p ≠ 0) (htau : tau = sigma * u ^ 2 / p ^ 2) :
    loewnerSigmaX p u sigma = loewnerX p tau ∧
      loewnerSigmaY p u sigma = loewnerY p tau ∧
      loewnerSigmaZ p u sigma = loewnerZ p tau ∧
      loewnerSigmaEll p u sigma = loewnerEll p tau := by
  subst tau
  have hX : loewnerSigmaX p u sigma =
      loewnerX p (sigma * u ^ 2 / p ^ 2) := by
    unfold loewnerSigmaX loewnerX
    field_simp [hp]
  have hY : loewnerSigmaY p u sigma =
      loewnerY p (sigma * u ^ 2 / p ^ 2) := by
    unfold loewnerSigmaY loewnerY
    field_simp [hp]
  have hZ : loewnerSigmaZ p u sigma =
      loewnerZ p (sigma * u ^ 2 / p ^ 2) := by
    unfold loewnerSigmaZ loewnerZ
    field_simp [hp]
  refine ⟨hX, hY, hZ, ?_⟩
  unfold loewnerSigmaEll loewnerEll
  rw [hY]

private theorem hasDerivAt_loewnerSigmaX
    (p u sigma : ℝ) :
    HasDerivAt (loewnerSigmaX p u) (-u ^ 2) sigma := by
  unfold loewnerSigmaX
  convert (hasDerivAt_const sigma (p ^ 2)).sub
    ((hasDerivAt_id sigma).mul_const (u ^ 2)) using 1 <;> ring

private theorem hasDerivAt_loewnerSigmaY
    (p u sigma : ℝ) :
    HasDerivAt (loewnerSigmaY p u) (-u ^ 2) sigma := by
  unfold loewnerSigmaY
  convert (hasDerivAt_const sigma ((1 - p) ^ 2)).sub
    ((hasDerivAt_id sigma).mul_const (u ^ 2)) using 1 <;> ring

private theorem hasDerivAt_loewnerSigmaZ
    (p u sigma : ℝ) :
    HasDerivAt (loewnerSigmaZ p u) (-u ^ 2) sigma := by
  unfold loewnerSigmaZ
  convert (hasDerivAt_const sigma (p * (1 - p))).sub
    ((hasDerivAt_id sigma).mul_const (u ^ 2)) using 1 <;> ring

private theorem hasDerivAt_loewnerSigmaEll
    {p u sigma : ℝ} (hY : loewnerSigmaY p u sigma ≠ 0) :
    HasDerivAt (loewnerSigmaEll p u)
      (u ^ 2 / loewnerSigmaY p u sigma) sigma := by
  have hlog := (Real.hasDerivAt_log hY).comp sigma
    (hasDerivAt_loewnerSigmaY p u sigma)
  unfold loewnerSigmaEll
  convert hlog.neg using 1
  field_simp [hY]

private theorem hasDerivAt_loewnerSigmaDelta
    {p u sigma : ℝ} (hY : loewnerSigmaY p u sigma ≠ 0) :
    HasDerivAt (loewnerSigmaDelta p u)
      (u ^ 2 / (2 * loewnerSigmaY p u sigma)) sigma := by
  unfold loewnerSigmaDelta
  convert (hasDerivAt_loewnerSigmaEll hY).div_const 2 using 1
  ring

/-- The `(1,1)` entry of equation (11). -/
theorem hasDerivAt_loewnerNormalizedG11
    {p u sigma tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (htauDef : tau = sigma * u ^ 2 / p ^ 2) :
    HasDerivAt (loewnerNormalizedG11 p u)
      ((1 / (loewnerX p tau * loewnerY p tau *
          (loewnerEll p tau / 2))) * loewnerB11 p tau u) sigma := by
  obtain ⟨hXval, hYval, hZval, hEllval⟩ :=
    loewnerSigma_values hp.1.ne' htauDef
  have hX := loewnerX_pos hp htau
  have hY := (loewnerY_mem_Ioo hp htau).1
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le (loewnerEll_ge_two_mul hp htau)
  have hDelta : loewnerSigmaDelta p u sigma ≠ 0 := by
    unfold loewnerSigmaDelta
    rw [hEllval]
    exact (div_pos hell (by norm_num)).ne'
  have hDeltaVal : loewnerSigmaDelta p u sigma = loewnerEll p tau / 2 := by
    unfold loewnerSigmaDelta
    rw [hEllval]
  have hden := ((hasDerivAt_loewnerSigmaX p u sigma).mul
    (hasDerivAt_loewnerSigmaY p u sigma)).mul
      (hasDerivAt_loewnerSigmaDelta (hYval.trans_ne hY.ne'))
  have hquot := (hasDerivAt_loewnerSigmaZ p u sigma).div hden
    (mul_ne_zero (mul_ne_zero (hXval.trans_ne hX.ne') (hYval.trans_ne hY.ne')) hDelta)
  unfold loewnerNormalizedG11
  convert hquot using 1
  simp only [Pi.mul_apply]
  rw [hXval, hYval, hZval, hDeltaVal]
  unfold loewnerB11 loewnerLeadingReserve loewnerR
  field_simp [hX.ne', hY.ne', hell.ne']
  ring

/-- The off-diagonal entry of equation (11). -/
theorem hasDerivAt_loewnerNormalizedG12
    {p u sigma tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (htauDef : tau = sigma * u ^ 2 / p ^ 2) :
    HasDerivAt (loewnerNormalizedG12 p u)
      ((1 / (loewnerX p tau * loewnerY p tau *
          (loewnerEll p tau / 2))) * loewnerB12 p tau u) sigma := by
  obtain ⟨hXval, hYval, _, hEllval⟩ :=
    loewnerSigma_values hp.1.ne' htauDef
  have hX := loewnerX_pos hp htau
  have hY := (loewnerY_mem_Ioo hp htau).1
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le (loewnerEll_ge_two_mul hp htau)
  have hDeltaVal : loewnerSigmaDelta p u sigma = loewnerEll p tau / 2 := by
    unfold loewnerSigmaDelta
    rw [hEllval]
  have hDelta : loewnerSigmaDelta p u sigma ≠ 0 := by
    rw [hDeltaVal]
    exact (div_pos hell (by norm_num)).ne'
  have hden := ((hasDerivAt_loewnerSigmaX p u sigma).mul
    (hasDerivAt_loewnerSigmaY p u sigma)).mul
      (hasDerivAt_loewnerSigmaDelta (hYval.trans_ne hY.ne'))
  have hnum : HasDerivAt (fun s : ℝ ↦ -s * u * (1 - 2 * p))
      (-u * (1 - 2 * p)) sigma := by
    convert (hasDerivAt_id sigma).const_mul (-u * (1 - 2 * p)) using 1
    · funext s
      simp [id_eq]
      ring
    · ring
  have hquot := hnum.div hden
    (mul_ne_zero (mul_ne_zero (hXval.trans_ne hX.ne') (hYval.trans_ne hY.ne')) hDelta)
  have hV : loewnerV p tau = sigma * u ^ 2 := by
    unfold loewnerV
    rw [htauDef]
    field_simp [hp.1.ne']
  unfold loewnerNormalizedG12
  convert hquot using 1
  simp only [Pi.mul_apply]
  rw [hXval, hYval, hDeltaVal]
  unfold loewnerB12 loewnerW loewnerR
  rw [hV]
  field_simp [hX.ne', hY.ne', hell.ne']
  ring

/-- The `(2,2)` entry of equation (11). -/
theorem hasDerivAt_loewnerNormalizedG22
    {p u sigma tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (htauDef : tau = sigma * u ^ 2 / p ^ 2) :
    HasDerivAt (loewnerNormalizedG22 p u)
      ((1 / (loewnerX p tau * loewnerY p tau *
          (loewnerEll p tau / 2))) * loewnerB22 p tau) sigma := by
  obtain ⟨hXval, hYval, hZval, hEllval⟩ :=
    loewnerSigma_values hp.1.ne' htauDef
  have hX := loewnerX_pos hp htau
  have hY := (loewnerY_mem_Ioo hp htau).1
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le (loewnerEll_ge_two_mul hp htau)
  have hDeltaVal : loewnerSigmaDelta p u sigma = loewnerEll p tau / 2 := by
    unfold loewnerSigmaDelta
    rw [hEllval]
  have hDelta : loewnerSigmaDelta p u sigma ≠ 0 := by
    rw [hDeltaVal]
    exact (div_pos hell (by norm_num)).ne'
  have hden := ((hasDerivAt_loewnerSigmaX p u sigma).mul
    (hasDerivAt_loewnerSigmaY p u sigma)).mul
      (hasDerivAt_loewnerSigmaDelta (hYval.trans_ne hY.ne'))
  have hnum := (hasDerivAt_id sigma).mul
    (hasDerivAt_loewnerSigmaZ p u sigma)
  have hquot := hnum.div hden
    (mul_ne_zero (mul_ne_zero (hXval.trans_ne hX.ne') (hYval.trans_ne hY.ne')) hDelta)
  have hV : loewnerV p tau = sigma * u ^ 2 := by
    unfold loewnerV
    rw [htauDef]
    field_simp [hp.1.ne']
  unfold loewnerNormalizedG22
  convert hquot using 1
  simp only [Pi.mul_apply, id_eq]
  rw [hXval, hYval, hZval, hDeltaVal]
  unfold loewnerB22 loewnerLeadingReserve loewnerR
  rw [hV]
  field_simp [hX.ne', hY.ne', hell.ne']
  ring

/-- Matrix-valued form of equation (11). -/
theorem hasDerivAt_loewnerNormalizedGMatrix
    {p u sigma tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (htauDef : tau = sigma * u ^ 2 / p ^ 2) :
    HasDerivAt (loewnerNormalizedGMatrix p u)
      (loewnerDerivativeMatrix p tau u) sigma := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  fin_cases i <;> fin_cases j
  · simpa [loewnerNormalizedGMatrix, loewnerDerivativeMatrix,
      loewnerDerivativeFactor] using
      hasDerivAt_loewnerNormalizedG11 hp htau htauDef
  · simpa [loewnerNormalizedGMatrix, loewnerDerivativeMatrix,
      loewnerDerivativeFactor] using
      hasDerivAt_loewnerNormalizedG12 hp htau htauDef
  · simpa [loewnerNormalizedGMatrix, loewnerDerivativeMatrix,
      loewnerDerivativeFactor] using
      hasDerivAt_loewnerNormalizedG12 hp htau htauDef
  · simpa [loewnerNormalizedGMatrix, loewnerDerivativeMatrix,
      loewnerDerivativeFactor] using
      hasDerivAt_loewnerNormalizedG22 hp htau htauDef

theorem loewnerDerivativeFactor_pos
    {p tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    0 < loewnerDerivativeFactor p tau := by
  have hell : 0 < loewnerEll p tau :=
    (mul_pos (by norm_num) hp.1).trans_le (loewnerEll_ge_two_mul hp htau)
  unfold loewnerDerivativeFactor
  exact one_div_pos.mpr
    (mul_pos (mul_pos (loewnerX_pos hp htau) (loewnerY_mem_Ioo hp htau).1)
      (div_pos hell (by norm_num)))

/-- Every derivative matrix is positive semidefinite on the physical cell. -/
theorem loewnerDerivativeMatrix_posSemidef
    {p tau u : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1) :
    Matrix.PosSemidef (loewnerDerivativeMatrix p tau u) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [loewnerDerivativeMatrix]
  · intro x
    have hq := loewnerB_quadratic_nonneg (p := p) (tau := tau) (u := u)
      (x := x 0) (y := x 1) hp htau
    have hf := (loewnerDerivativeFactor_pos hp htau).le
    simp [loewnerDerivativeMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      mul_add]
    nlinarith [mul_nonneg hf hq]

theorem hasDerivAt_loewnerNormalizedQuadratic
    {p u x y sigma tau : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (htau : tau ∈ Ico (0 : ℝ) 1)
    (htauDef : tau = sigma * u ^ 2 / p ^ 2) :
    HasDerivAt (loewnerNormalizedQuadratic p u x y)
      (loewnerDerivativeFactor p tau *
        (loewnerB11 p tau u * x ^ 2 +
          2 * loewnerB12 p tau u * x * y +
          loewnerB22 p tau * y ^ 2)) sigma := by
  have h11 := (hasDerivAt_loewnerNormalizedG11 hp htau htauDef).mul_const (x ^ 2)
  have h12 := (hasDerivAt_loewnerNormalizedG12 hp htau htauDef).mul_const
    (2 * x * y)
  have h22 := (hasDerivAt_loewnerNormalizedG22 hp htau htauDef).mul_const (y ^ 2)
  unfold loewnerNormalizedQuadratic
  convert (h11.add h12).add h22 using 1
  · funext s
    simp only [Pi.add_apply]
    ring
  · unfold loewnerDerivativeFactor
    ring

theorem loewnerNormalizedQuadratic_monotoneOn
    {p u x y sigma₁ sigma₂ : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hphysical : ∀ sigma ∈ Icc sigma₁ sigma₂,
      sigma * u ^ 2 / p ^ 2 ∈ Ico (0 : ℝ) 1) :
    MonotoneOn (loewnerNormalizedQuadratic p u x y) (Icc sigma₁ sigma₂) := by
  let tau : ℝ → ℝ := fun sigma ↦ sigma * u ^ 2 / p ^ 2
  have hderiv : ∀ sigma ∈ Icc sigma₁ sigma₂,
      HasDerivAt (loewnerNormalizedQuadratic p u x y)
        (loewnerDerivativeFactor p (tau sigma) *
          (loewnerB11 p (tau sigma) u * x ^ 2 +
            2 * loewnerB12 p (tau sigma) u * x * y +
            loewnerB22 p (tau sigma) * y ^ 2)) sigma := by
    intro sigma hs
    exact hasDerivAt_loewnerNormalizedQuadratic hp (hphysical sigma hs) rfl
  apply monotoneOn_of_deriv_nonneg (convex_Icc sigma₁ sigma₂)
  · intro sigma hs
    exact (hderiv sigma hs).continuousAt.continuousWithinAt
  · intro sigma hs
    rw [interior_Icc] at hs
    exact (hderiv sigma ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
  · intro sigma hs
    rw [interior_Icc] at hs
    rw [(hderiv sigma ⟨hs.1.le, hs.2.le⟩).deriv]
    exact mul_nonneg
      (loewnerDerivativeFactor_pos hp (hphysical sigma ⟨hs.1.le, hs.2.le⟩)).le
      (loewnerB_quadratic_nonneg hp (hphysical sigma ⟨hs.1.le, hs.2.le⟩))

theorem loewnerNormalizedQuadratic_strictMonoOn
    {p u x y sigma₁ sigma₂ : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hu : u ≠ 0) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hphysical : ∀ sigma ∈ Icc sigma₁ sigma₂,
      sigma * u ^ 2 / p ^ 2 ∈ Ico (0 : ℝ) 1) :
    StrictMonoOn (loewnerNormalizedQuadratic p u x y)
      (Icc sigma₁ sigma₂) := by
  let tau : ℝ → ℝ := fun sigma ↦ sigma * u ^ 2 / p ^ 2
  let hp' : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) := ⟨hp.1, hp.2.le⟩
  have hderiv : ∀ sigma ∈ Icc sigma₁ sigma₂,
      HasDerivAt (loewnerNormalizedQuadratic p u x y)
        (loewnerDerivativeFactor p (tau sigma) *
          (loewnerB11 p (tau sigma) u * x ^ 2 +
            2 * loewnerB12 p (tau sigma) u * x * y +
            loewnerB22 p (tau sigma) * y ^ 2)) sigma := by
    intro sigma hs
    exact hasDerivAt_loewnerNormalizedQuadratic hp' (hphysical sigma hs) rfl
  apply strictMonoOn_of_deriv_pos (convex_Icc sigma₁ sigma₂)
  · intro sigma hs
    exact (hderiv sigma hs).continuousAt.continuousWithinAt
  · intro sigma hs
    rw [interior_Icc] at hs
    rw [(hderiv sigma ⟨hs.1.le, hs.2.le⟩).deriv]
    exact mul_pos
      (loewnerDerivativeFactor_pos hp' (hphysical sigma ⟨hs.1.le, hs.2.le⟩))
      (two_by_two_quadratic_pos
        (loewnerB11_nonneg hp' (hphysical sigma ⟨hs.1.le, hs.2.le⟩))
        (loewnerB22_pos hp' (hphysical sigma ⟨hs.1.le, hs.2.le⟩)).le
        (loewnerBDet_pos hp (hphysical sigma ⟨hs.1.le, hs.2.le⟩) hu)
        hxy)

theorem loewnerNormalizedQuadratic_lt
    {p u x y sigma₁ sigma₂ : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hu : u ≠ 0) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hsigma : sigma₁ < sigma₂)
    (hphysical : ∀ sigma ∈ Icc sigma₁ sigma₂,
      sigma * u ^ 2 / p ^ 2 ∈ Ico (0 : ℝ) 1) :
    loewnerNormalizedQuadratic p u x y sigma₁ <
      loewnerNormalizedQuadratic p u x y sigma₂ :=
  loewnerNormalizedQuadratic_strictMonoOn hp hu hxy hphysical
    (left_mem_Icc.2 hsigma.le) (right_mem_Icc.2 hsigma.le) hsigma

/-- Integrated Loewner monotonicity of the normalized entropy Hessian family. -/
theorem loewnerNormalizedGMatrix_mono
    {p u sigma₁ sigma₂ : ℝ}
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hsigma : sigma₁ ≤ sigma₂)
    (hphysical : ∀ sigma ∈ Icc sigma₁ sigma₂,
      sigma * u ^ 2 / p ^ 2 ∈ Ico (0 : ℝ) 1) :
    MatrixLoewnerLE (loewnerNormalizedGMatrix p u sigma₁)
      (loewnerNormalizedGMatrix p u sigma₂) := by
  unfold MatrixLoewnerLE
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [loewnerNormalizedGMatrix, Matrix.conjTranspose, Matrix.sub_apply]
  · intro v
    have hmono := loewnerNormalizedQuadratic_monotoneOn
      (p := p) (u := u) (x := v 0) (y := v 1) hp hphysical
    have hle := hmono (left_mem_Icc.2 hsigma) (right_mem_Icc.2 hsigma) hsigma
    unfold loewnerNormalizedQuadratic at hle
    simp [loewnerNormalizedGMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.sub_apply, mul_add]
    nlinarith

end CourtadeKumar
