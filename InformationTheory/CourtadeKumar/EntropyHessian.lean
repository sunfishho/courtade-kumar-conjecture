import InformationTheory.CourtadeKumar.LoewnerDerivative

/-! Directional second derivatives of the two-point entropy and their Hessian matrix. -/

open Set

namespace CourtadeKumar

noncomputable def natEntropySlope (q : ℝ) : ℝ :=
  Real.log (1 - q) - Real.log q

theorem hasDerivAt_natEntropySlope
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt natEntropySlope (-1 / (q * (1 - q))) q := by
  have hone : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.symm
  have hleft : HasDerivAt (fun s : ℝ ↦ Real.log (1 - s))
      (-1 / (1 - q)) q := by
    have hinner : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) q := by
      convert (hasDerivAt_const q 1).sub (hasDerivAt_id q) using 1 <;> ring
    convert (Real.hasDerivAt_log hone).comp q hinner using 1
    field_simp [hone]
  unfold natEntropySlope
  convert hleft.sub (Real.hasDerivAt_log hq0) using 1
  field_simp [hq0, hone]
  ring

noncomputable def scaledNatEntropy (c p u : ℝ) : ℝ :=
  (Real.binEntropy (p - c * u) + Real.binEntropy (p + c * u)) / 2

noncomputable def scaledNatEntropyAlong
    (c p u x y t : ℝ) : ℝ :=
  scaledNatEntropy c (p + t * x) (u + t * y)

noncomputable def scaledNatEntropyDirectionalFirst
    (c p u x y t : ℝ) : ℝ :=
  ((x - c * y) * natEntropySlope (p + t * x - c * (u + t * y)) +
    (x + c * y) * natEntropySlope (p + t * x + c * (u + t * y))) / 2

noncomputable def scaledNatEntropyNegCurvature
    (c p u x y : ℝ) : ℝ :=
  ((x - c * y) ^ 2 /
      ((p - c * u) * (1 - (p - c * u))) +
    (x + c * y) ^ 2 /
      ((p + c * u) * (1 - (p + c * u)))) / 2

theorem hasDerivAt_scaledNatEntropyAlong
    {c p u x y t : ℝ}
    (hminus : p + t * x - c * (u + t * y) ∈ Ioo (0 : ℝ) 1)
    (hplus : p + t * x + c * (u + t * y) ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (scaledNatEntropyAlong c p u x y)
      (scaledNatEntropyDirectionalFirst c p u x y t) t := by
  have hargMinus : HasDerivAt
      (fun s : ℝ ↦ p + s * x - c * (u + s * y)) (x - c * y) t := by
    have hu : HasDerivAt (fun s : ℝ ↦ c * (u + s * y)) (c * y) t := by
      convert (((hasDerivAt_const t u).add
        ((hasDerivAt_id t).mul_const y)).const_mul c) using 1 <;> ring
    convert (((hasDerivAt_const t p).add
      ((hasDerivAt_id t).mul_const x)).sub hu) using 1 <;> ring
  have hargPlus : HasDerivAt
      (fun s : ℝ ↦ p + s * x + c * (u + s * y)) (x + c * y) t := by
    have hu : HasDerivAt (fun s : ℝ ↦ c * (u + s * y)) (c * y) t := by
      convert (((hasDerivAt_const t u).add
        ((hasDerivAt_id t).mul_const y)).const_mul c) using 1 <;> ring
    convert (((hasDerivAt_const t p).add
      ((hasDerivAt_id t).mul_const x)).add hu) using 1 <;> ring
  have hm := (Real.hasDerivAt_binEntropy hminus.1.ne' hminus.2.ne).comp t hargMinus
  have hp := (Real.hasDerivAt_binEntropy hplus.1.ne' hplus.2.ne).comp t hargPlus
  unfold scaledNatEntropyAlong scaledNatEntropy scaledNatEntropyDirectionalFirst
    natEntropySlope
  convert (hm.add hp).div_const 2 using 1 <;>
    simp [Function.comp_apply, Real.deriv_binEntropy] <;> ring

theorem hasDerivAt_scaledNatEntropyDirectionalFirst
    {c p u x y : ℝ}
    (hminus : p - c * u ∈ Ioo (0 : ℝ) 1)
    (hplus : p + c * u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (scaledNatEntropyDirectionalFirst c p u x y)
      (-scaledNatEntropyNegCurvature c p u x y) 0 := by
  have hargMinus : HasDerivAt
      (fun s : ℝ ↦ p + s * x - c * (u + s * y)) (x - c * y) 0 := by
    have hu : HasDerivAt (fun s : ℝ ↦ c * (u + s * y)) (c * y) 0 := by
      convert (((hasDerivAt_const 0 u).add
        ((hasDerivAt_id 0).mul_const y)).const_mul c) using 1 <;> ring
    convert (((hasDerivAt_const 0 p).add
      ((hasDerivAt_id 0).mul_const x)).sub hu) using 1 <;> ring
  have hargPlus : HasDerivAt
      (fun s : ℝ ↦ p + s * x + c * (u + s * y)) (x + c * y) 0 := by
    have hu : HasDerivAt (fun s : ℝ ↦ c * (u + s * y)) (c * y) 0 := by
      convert (((hasDerivAt_const 0 u).add
        ((hasDerivAt_id 0).mul_const y)).const_mul c) using 1 <;> ring
    convert (((hasDerivAt_const 0 p).add
      ((hasDerivAt_id 0).mul_const x)).add hu) using 1 <;> ring
  have hsMinus : HasDerivAt natEntropySlope
      (-1 / ((p - c * u) * (1 - (p - c * u))))
      (p + 0 * x - c * (u + 0 * y)) := by
    simpa using hasDerivAt_natEntropySlope hminus.1.ne' hminus.2.ne
  have hsPlus : HasDerivAt natEntropySlope
      (-1 / ((p + c * u) * (1 - (p + c * u))))
      (p + 0 * x + c * (u + 0 * y)) := by
    simpa using hasDerivAt_natEntropySlope hplus.1.ne' hplus.2.ne
  have hm := (hsMinus.comp 0 hargMinus).const_mul (x - c * y)
  have hp := (hsPlus.comp 0 hargPlus).const_mul (x + c * y)
  unfold scaledNatEntropyDirectionalFirst scaledNatEntropyNegCurvature
  convert (hm.add hp).div_const 2 using 1
  field_simp [hminus.1.ne', hminus.2.ne, hplus.1.ne', hplus.2.ne]
  ring

noncomputable def loewnerGQuadratic
    (p u x y sigma : ℝ) : ℝ :=
  (loewnerSigmaZ p u sigma * x ^ 2 -
      2 * sigma * u * (1 - 2 * p) * x * y +
      sigma * loewnerSigmaZ p u sigma * y ^ 2) /
    (loewnerSigmaX p u sigma * loewnerSigmaY p u sigma)

/-- The negative entropy curvature is exactly the quadratic form of `G_sigma`. -/
theorem scaledNatEntropyNegCurvature_eq_loewner
    {c p u x y : ℝ}
    (hminus : p - c * u ≠ 0) (hminus1 : p - c * u ≠ 1)
    (hplus : p + c * u ≠ 0) (hplus1 : p + c * u ≠ 1) :
    scaledNatEntropyNegCurvature c p u x y =
      loewnerGQuadratic p u x y (c ^ 2) := by
  unfold scaledNatEntropyNegCurvature loewnerGQuadratic loewnerSigmaX
    loewnerSigmaY loewnerSigmaZ
  have hX : p ^ 2 - c ^ 2 * u ^ 2 ≠ 0 := by
    rw [show p ^ 2 - c ^ 2 * u ^ 2 = (p - c * u) * (p + c * u) by ring]
    exact mul_ne_zero hminus hplus
  have hY : (1 - p) ^ 2 - c ^ 2 * u ^ 2 ≠ 0 := by
    rw [show (1 - p) ^ 2 - c ^ 2 * u ^ 2 =
      (1 - (p - c * u)) * (1 - (p + c * u)) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hminus1.symm)
      (sub_ne_zero.mpr hplus1.symm)
  have hmden : (p - c * u) * (1 - (p - c * u)) ≠ 0 :=
    mul_ne_zero hminus (sub_ne_zero.mpr hminus1.symm)
  have hpden : (p + c * u) * (1 - (p + c * u)) ≠ 0 :=
    mul_ne_zero hplus (sub_ne_zero.mpr hplus1.symm)
  have hXeq : p ^ 2 - c ^ 2 * u ^ 2 =
      (p - c * u) * (p + c * u) := by ring
  have hYeq : (1 - p) ^ 2 - c ^ 2 * u ^ 2 =
      (1 - (p - c * u)) * (1 - (p + c * u)) := by ring
  rw [hXeq, hYeq]
  field_simp [hminus, hplus, sub_ne_zero.mpr hminus1.symm,
    sub_ne_zero.mpr hplus1.symm, hmden, hpden]
  ring

theorem loewnerGQuadratic_eq_normalized
    {p u x y sigma : ℝ}
    (hDelta : loewnerSigmaDelta p u sigma ≠ 0) :
    loewnerGQuadratic p u x y sigma =
      loewnerSigmaDelta p u sigma *
        loewnerNormalizedQuadratic p u x y sigma := by
  unfold loewnerGQuadratic loewnerNormalizedQuadratic
    loewnerNormalizedG11 loewnerNormalizedG12 loewnerNormalizedG22
  field_simp [hDelta]
  ring

end CourtadeKumar
