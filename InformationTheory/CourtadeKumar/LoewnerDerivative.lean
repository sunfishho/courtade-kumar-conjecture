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

end CourtadeKumar
