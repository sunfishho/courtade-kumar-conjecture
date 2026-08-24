import InformationTheory.CourtadeKumar.SingleRayContactAlgebra
import InformationTheory.CourtadeKumar.EntropyHessian

/-! Quadratic contraction of a symmetric binary-entropy drop. -/

open Set

namespace CourtadeKumar

noncomputable def symmetricEntropyDropNat (m u : ℝ) : ℝ :=
  Real.binEntropy m -
    (Real.binEntropy (m - u) + Real.binEntropy (m + u)) / 2

noncomputable def symmetricEntropyDropSlope (m u : ℝ) : ℝ :=
  (natEntropySlope (m - u) - natEntropySlope (m + u)) / 2

noncomputable def entropyCurvature (p : ℝ) : ℝ :=
  1 / (p * (1 - p))

noncomputable def entropyCurvatureDeriv (p : ℝ) : ℝ :=
  (2 * p - 1) / (p ^ 2 * (1 - p) ^ 2)

noncomputable def entropyCurvatureDeriv2 (p : ℝ) : ℝ :=
  2 * (3 * p ^ 2 - 3 * p + 1) / (p ^ 3 * (1 - p) ^ 3)

noncomputable def symmetricEntropyDropCurvature (m u : ℝ) : ℝ :=
  (entropyCurvature (m - u) + entropyCurvature (m + u)) / 2

noncomputable def symmetricEntropyDropCurvatureDeriv (m u : ℝ) : ℝ :=
  (entropyCurvatureDeriv (m + u) -
    entropyCurvatureDeriv (m - u)) / 2

noncomputable def symmetricEntropyDropQuadraticSlopeGap (m u : ℝ) : ℝ :=
  u * symmetricEntropyDropCurvature m u - symmetricEntropyDropSlope m u

noncomputable def symmetricEntropyDropRatioSlopeGap (m u : ℝ) : ℝ :=
  u * symmetricEntropyDropSlope m u - 2 * symmetricEntropyDropNat m u

noncomputable def symmetricEntropyDropRatio (m u : ℝ) : ℝ :=
  symmetricEntropyDropNat m u / u ^ 2

theorem hasDerivAt_symmetricEntropyDropNat
    {m u : ℝ} (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (symmetricEntropyDropNat m)
      (symmetricEntropyDropSlope m u) u := by
  have hargMinus : HasDerivAt (fun w : ℝ ↦ m - w) (-1) u :=
    (hasDerivAt_id u).const_sub m
  have hargPlus : HasDerivAt (fun w : ℝ ↦ m + w) 1 u :=
    (hasDerivAt_id u).const_add m
  have hminus' := (Real.hasDerivAt_binEntropy hminus.1.ne' hminus.2.ne).comp
    u hargMinus
  have hplus' := (Real.hasDerivAt_binEntropy hplus.1.ne' hplus.2.ne).comp
    u hargPlus
  unfold symmetricEntropyDropNat symmetricEntropyDropSlope natEntropySlope
  convert (hasDerivAt_const u (Real.binEntropy m)).sub
    ((hminus'.add hplus').div_const 2) using 1 <;>
    simp [Real.deriv_binEntropy] <;> ring

theorem hasDerivAt_symmetricEntropyDropSlope
    {m u : ℝ} (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (symmetricEntropyDropSlope m)
      (symmetricEntropyDropCurvature m u) u := by
  have hargMinus : HasDerivAt (fun w : ℝ ↦ m - w) (-1) u :=
    (hasDerivAt_id u).const_sub m
  have hargPlus : HasDerivAt (fun w : ℝ ↦ m + w) 1 u :=
    (hasDerivAt_id u).const_add m
  have hminus' := (hasDerivAt_natEntropySlope
    hminus.1.ne' hminus.2.ne).comp u hargMinus
  have hplus' := (hasDerivAt_natEntropySlope
    hplus.1.ne' hplus.2.ne).comp u hargPlus
  unfold symmetricEntropyDropSlope symmetricEntropyDropCurvature entropyCurvature
  convert (hminus'.sub hplus').div_const 2 using 1
  field_simp [hminus.1.ne', hminus.2.ne, hplus.1.ne', hplus.2.ne]
  ring

theorem hasDerivAt_entropyCurvature
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt entropyCurvature (entropyCurvatureDeriv p) p := by
  have hden : p * (1 - p) ≠ 0 :=
    mul_ne_zero hp.1.ne' (by linarith [hp.2])
  have hinner : HasDerivAt (fun q : ℝ ↦ q * (1 - q)) (1 - 2 * p) p := by
    convert (hasDerivAt_id p).mul
      ((hasDerivAt_const p 1).sub (hasDerivAt_id p)) using 1 <;>
      simp [id_eq] <;> ring
  unfold entropyCurvature entropyCurvatureDeriv
  convert (hasDerivAt_const p 1).div hinner hden using 1
  field_simp [hp.1.ne', (by linarith [hp.2] : 1 - p ≠ 0)]
  ring

theorem hasDerivAt_entropyCurvatureDeriv
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt entropyCurvatureDeriv (entropyCurvatureDeriv2 p) p := by
  have hOne : HasDerivAt (fun q : ℝ ↦ 1 - q) (-1) p :=
    (hasDerivAt_id p).const_sub 1
  have hnum : HasDerivAt (fun q : ℝ ↦ 2 * q - 1) 2 p := by
    convert ((hasDerivAt_id p).const_mul 2).sub_const 1 using 1 <;> ring
  have hp2 := (hasDerivAt_id p).pow 2
  have hOne2 := hOne.pow 2
  have hden : HasDerivAt (fun q : ℝ ↦ q ^ 2 * (1 - q) ^ 2)
      (2 * p * (1 - p) ^ 2 - 2 * p ^ 2 * (1 - p)) p := by
    convert hp2.mul hOne2 using 1 <;> simp [id_eq] <;> ring
  have hdenNe : p ^ 2 * (1 - p) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hp.1.ne')
      (pow_ne_zero 2 (by linarith [hp.2] : 1 - p ≠ 0))
  unfold entropyCurvatureDeriv entropyCurvatureDeriv2
  convert hnum.div hden hdenNe using 1
  field_simp [hp.1.ne', (by linarith [hp.2] : 1 - p ≠ 0)]
  ring

theorem entropyCurvatureDeriv2_pos
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < entropyCurvatureDeriv2 p := by
  unfold entropyCurvatureDeriv2
  have hpoly : 0 < 3 * p ^ 2 - 3 * p + 1 := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  exact div_pos (mul_pos (by norm_num) hpoly)
    (mul_pos (pow_pos hp.1 3) (pow_pos (by linarith [hp.2]) 3))

theorem strictMonoOn_entropyCurvatureDeriv :
    StrictMonoOn entropyCurvatureDeriv (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro p hp
    exact (hasDerivAt_entropyCurvatureDeriv hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(hasDerivAt_entropyCurvatureDeriv hp).deriv]
    exact entropyCurvatureDeriv2_pos hp

lemma symmetricEntropyDrop_width_args
    {m U u : ℝ} (hU : 0 ≤ U) (hminusU : 0 < m - U)
    (hplusU : m + U < 1) (hu : u ∈ Icc (0 : ℝ) U) :
    m - u ∈ Ioo (0 : ℝ) 1 ∧ m + u ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · constructor
    · linarith [hu.2]
    · linarith [hplusU, hU, hu.1]
  · constructor
    · linarith [hminusU, hU, hu.1]
    · linarith [hu.2]

theorem hasDerivAt_symmetricEntropyDropCurvature
    {m u : ℝ} (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (symmetricEntropyDropCurvature m)
      (symmetricEntropyDropCurvatureDeriv m u) u := by
  have hargMinus : HasDerivAt (fun w : ℝ ↦ m - w) (-1) u :=
    (hasDerivAt_id u).const_sub m
  have hargPlus : HasDerivAt (fun w : ℝ ↦ m + w) 1 u :=
    (hasDerivAt_id u).const_add m
  have hminus' := (hasDerivAt_entropyCurvature hminus).comp u hargMinus
  have hplus' := (hasDerivAt_entropyCurvature hplus).comp u hargPlus
  unfold symmetricEntropyDropCurvature symmetricEntropyDropCurvatureDeriv
  convert (hminus'.add hplus').div_const 2 using 1 <;> ring

theorem symmetricEntropyDropCurvatureDeriv_nonneg
    {m u : ℝ} (hu : 0 ≤ u)
    (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ symmetricEntropyDropCurvatureDeriv m u := by
  have hmono := strictMonoOn_entropyCurvatureDeriv.monotoneOn
    hminus hplus (by linarith [hu])
  unfold symmetricEntropyDropCurvatureDeriv
  linarith

theorem monotoneOn_symmetricEntropyDropCurvature
    {m U : ℝ} (hU : 0 ≤ U) (hminusU : 0 < m - U)
    (hplusU : m + U < 1) :
    MonotoneOn (symmetricEntropyDropCurvature m) (Icc (0 : ℝ) U) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) U)
  · intro u hu
    obtain ⟨hminus, hplus⟩ :=
      symmetricEntropyDrop_width_args hU hminusU hplusU hu
    exact (hasDerivAt_symmetricEntropyDropCurvature hminus hplus).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    have hu' : u ∈ Icc (0 : ℝ) U := ⟨hu.1.le, hu.2.le⟩
    obtain ⟨hminus, hplus⟩ :=
      symmetricEntropyDrop_width_args hU hminusU hplusU hu'
    exact (hasDerivAt_symmetricEntropyDropCurvature hminus hplus).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    have hu' : u ∈ Icc (0 : ℝ) U := ⟨hu.1.le, hu.2.le⟩
    obtain ⟨hminus, hplus⟩ :=
      symmetricEntropyDrop_width_args hU hminusU hplusU hu'
    rw [(hasDerivAt_symmetricEntropyDropCurvature hminus hplus).deriv]
    exact symmetricEntropyDropCurvatureDeriv_nonneg hu.1.le hminus hplus

theorem hasDerivAt_symmetricEntropyDropQuadraticSlopeGap
    {m u : ℝ} (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (symmetricEntropyDropQuadraticSlopeGap m)
      (u * symmetricEntropyDropCurvatureDeriv m u) u := by
  have hcurv := hasDerivAt_symmetricEntropyDropCurvature hminus hplus
  have hslope := hasDerivAt_symmetricEntropyDropSlope hminus hplus
  unfold symmetricEntropyDropQuadraticSlopeGap
  convert ((hasDerivAt_id u).mul hcurv).sub hslope using 1 <;>
    simp [id_eq] <;> ring

@[simp] theorem symmetricEntropyDropSlope_zero (m : ℝ) :
    symmetricEntropyDropSlope m 0 = 0 := by
  simp [symmetricEntropyDropSlope]

@[simp] theorem symmetricEntropyDropQuadraticSlopeGap_zero (m : ℝ) :
    symmetricEntropyDropQuadraticSlopeGap m 0 = 0 := by
  simp [symmetricEntropyDropQuadraticSlopeGap]

theorem symmetricEntropyDropQuadraticSlopeGap_nonneg
    {m U u : ℝ} (hU : 0 ≤ U) (hminusU : 0 < m - U)
    (hplusU : m + U < 1) (hu : u ∈ Icc (0 : ℝ) U) :
    0 ≤ symmetricEntropyDropQuadraticSlopeGap m u := by
  have hmono : MonotoneOn (symmetricEntropyDropQuadraticSlopeGap m)
      (Icc (0 : ℝ) U) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) U)
    · intro w hw
      obtain ⟨hminus, hplus⟩ :=
        symmetricEntropyDrop_width_args hU hminusU hplusU hw
      exact (hasDerivAt_symmetricEntropyDropQuadraticSlopeGap
        hminus hplus).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw' : w ∈ Icc (0 : ℝ) U := ⟨hw.1.le, hw.2.le⟩
      obtain ⟨hminus, hplus⟩ :=
        symmetricEntropyDrop_width_args hU hminusU hplusU hw'
      exact (hasDerivAt_symmetricEntropyDropQuadraticSlopeGap
        hminus hplus).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw' : w ∈ Icc (0 : ℝ) U := ⟨hw.1.le, hw.2.le⟩
      obtain ⟨hminus, hplus⟩ :=
        symmetricEntropyDrop_width_args hU hminusU hplusU hw'
      rw [(hasDerivAt_symmetricEntropyDropQuadraticSlopeGap hminus hplus).deriv]
      exact mul_nonneg hw.1.le
        (symmetricEntropyDropCurvatureDeriv_nonneg hw.1.le hminus hplus)
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) U := ⟨le_rfl, hU⟩
  simpa using hmono hzero hu hu.1

theorem hasDerivAt_symmetricEntropyDropRatioSlopeGap
    {m u : ℝ} (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (symmetricEntropyDropRatioSlopeGap m)
      (symmetricEntropyDropQuadraticSlopeGap m u) u := by
  have hdrop := hasDerivAt_symmetricEntropyDropNat hminus hplus
  have hslope := hasDerivAt_symmetricEntropyDropSlope hminus hplus
  unfold symmetricEntropyDropRatioSlopeGap
    symmetricEntropyDropQuadraticSlopeGap
  convert ((hasDerivAt_id u).mul hslope).sub (hdrop.const_mul 2) using 1 <;>
    simp [id_eq] <;> ring

@[simp] theorem symmetricEntropyDropNat_zero (m : ℝ) :
    symmetricEntropyDropNat m 0 = 0 := by
  simp [symmetricEntropyDropNat]

@[simp] theorem symmetricEntropyDropRatioSlopeGap_zero (m : ℝ) :
    symmetricEntropyDropRatioSlopeGap m 0 = 0 := by
  simp [symmetricEntropyDropRatioSlopeGap]

theorem symmetricEntropyDropRatioSlopeGap_nonneg
    {m U u : ℝ} (hU : 0 ≤ U) (hminusU : 0 < m - U)
    (hplusU : m + U < 1) (hu : u ∈ Icc (0 : ℝ) U) :
    0 ≤ symmetricEntropyDropRatioSlopeGap m u := by
  have hmono : MonotoneOn (symmetricEntropyDropRatioSlopeGap m)
      (Icc (0 : ℝ) U) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) U)
    · intro w hw
      obtain ⟨hminus, hplus⟩ :=
        symmetricEntropyDrop_width_args hU hminusU hplusU hw
      exact (hasDerivAt_symmetricEntropyDropRatioSlopeGap
        hminus hplus).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw' : w ∈ Icc (0 : ℝ) U := ⟨hw.1.le, hw.2.le⟩
      obtain ⟨hminus, hplus⟩ :=
        symmetricEntropyDrop_width_args hU hminusU hplusU hw'
      exact (hasDerivAt_symmetricEntropyDropRatioSlopeGap
        hminus hplus).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw' : w ∈ Icc (0 : ℝ) U := ⟨hw.1.le, hw.2.le⟩
      obtain ⟨hminus, hplus⟩ :=
        symmetricEntropyDrop_width_args hU hminusU hplusU hw'
      rw [(hasDerivAt_symmetricEntropyDropRatioSlopeGap hminus hplus).deriv]
      exact symmetricEntropyDropQuadraticSlopeGap_nonneg
        hU hminusU hplusU hw'
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) U := ⟨le_rfl, hU⟩
  simpa using hmono hzero hu hu.1

theorem hasDerivAt_symmetricEntropyDropRatio
    {m u : ℝ} (hu : u ≠ 0)
    (hminus : m - u ∈ Ioo (0 : ℝ) 1)
    (hplus : m + u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (symmetricEntropyDropRatio m)
      (symmetricEntropyDropRatioSlopeGap m u / u ^ 3) u := by
  have hdrop := hasDerivAt_symmetricEntropyDropNat hminus hplus
  have hden : HasDerivAt (fun w : ℝ ↦ w ^ 2) (2 * u) u := by
    convert (hasDerivAt_id u).pow 2 using 1 <;> simp [id_eq] <;> ring
  unfold symmetricEntropyDropRatio symmetricEntropyDropRatioSlopeGap
  convert hdrop.div hden (pow_ne_zero 2 hu) using 1
  field_simp [hu]

theorem monotoneOn_symmetricEntropyDropRatio
    {m a U : ℝ} (ha : 0 < a) (haU : a ≤ U)
    (hminusU : 0 < m - U) (hplusU : m + U < 1) :
    MonotoneOn (symmetricEntropyDropRatio m) (Icc a U) := by
  have hU : 0 ≤ U := le_trans ha.le haU
  apply monotoneOn_of_deriv_nonneg (convex_Icc a U)
  · intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hu.1)
    obtain ⟨hminus, hplus⟩ :=
      symmetricEntropyDrop_width_args hU hminusU hplusU
        ⟨(le_trans ha.le hu.1), hu.2⟩
    exact (hasDerivAt_symmetricEntropyDropRatio hu0 hminus hplus).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans ha hu.1)
    obtain ⟨hminus, hplus⟩ :=
      symmetricEntropyDrop_width_args hU hminusU hplusU
        ⟨(le_trans ha.le hu.1.le), hu.2.le⟩
    exact (hasDerivAt_symmetricEntropyDropRatio hu0 hminus hplus).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans ha hu.1)
    have huIcc : u ∈ Icc (0 : ℝ) U :=
      ⟨le_trans ha.le hu.1.le, hu.2.le⟩
    obtain ⟨hminus, hplus⟩ :=
      symmetricEntropyDrop_width_args hU hminusU hplusU huIcc
    rw [(hasDerivAt_symmetricEntropyDropRatio hu0 hminus hplus).deriv]
    exact div_nonneg
      (symmetricEntropyDropRatioSlopeGap_nonneg hU hminusU hplusU huIcc)
      (pow_nonneg (le_trans ha.le hu.1.le) 3)

theorem symmetricEntropyDrop_quadratic_contraction
    {m u rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) (hu : 0 < u)
    (hminus : 0 < m - u) (hplus : m + u < 1) :
    symmetricEntropyDropNat m (rho * u) ≤
      rho ^ 2 * symmetricEntropyDropNat m u := by
  rcases eq_or_lt_of_le hrho.1 with rfl | hrho0
  · simp
  · have hrhou : 0 < rho * u := mul_pos hrho0 hu
    have hrhou_le : rho * u ≤ u := by
      exact mul_le_of_le_one_left hu.le hrho.2
    have hmono := monotoneOn_symmetricEntropyDropRatio
      hrhou hrhou_le hminus hplus
    have hratio := hmono ⟨le_rfl, hrhou_le⟩ ⟨hrhou_le, le_rfl⟩ hrhou_le
    unfold symmetricEntropyDropRatio at hratio
    have hcross := (div_le_div_iff₀ (sq_pos_of_pos hrhou)
      (sq_pos_of_pos hu)).mp hratio
    apply le_of_mul_le_mul_right
    · calc
        symmetricEntropyDropNat m (rho * u) * u ^ 2
            ≤ symmetricEntropyDropNat m u * (rho * u) ^ 2 := hcross
        _ = (rho ^ 2 * symmetricEntropyDropNat m u) * u ^ 2 := by ring
    · exact sq_pos_of_pos hu

theorem symmetricEntropyDropNat_eq_radial (c r z : ℝ) :
    symmetricEntropyDropNat z (c * r * z) =
      Real.binEntropy z - radialNatEntropy c r z := by
  unfold symmetricEntropyDropNat radialNatEntropy
  congr 3 <;> ring

/-- Contracting the radial separation by `rho` contracts the symmetric
entropy drop by at least the quadratic factor `rho²`. -/
theorem radialNatEntropyDrop_quadratic_contraction
    {rho r z : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    Real.binEntropy z - radialNatEntropy rho r z ≤
      rho ^ 2 * (Real.binEntropy z - radialNatEntropy 1 r z) := by
  have hu : 0 < r * z := mul_pos hr.1 hz.1
  have hminus : 0 < z - r * z := by
    nlinarith [mul_pos (sub_pos.mpr hr.2) hz.1]
  have hplus : z + r * z < 1 := by
    have hfactor : 1 + r < 2 := by linarith [hr.2]
    calc
      z + r * z = (1 + r) * z := by ring
      _ < 2 * z := mul_lt_mul_of_pos_right hfactor hz.1
      _ < 1 := by linarith [hz.2]
  have hcontract := symmetricEntropyDrop_quadratic_contraction
    hrho hu hminus hplus
  have hright : symmetricEntropyDropNat z (r * z) =
      Real.binEntropy z - radialNatEntropy 1 r z := by
    simpa using symmetricEntropyDropNat_eq_radial 1 r z
  have hleft : symmetricEntropyDropNat z (rho * (r * z)) =
      Real.binEntropy z - radialNatEntropy rho r z := by
    rw [show rho * (r * z) = rho * r * z by ring]
    exact symmetricEntropyDropNat_eq_radial rho r z
  rw [hleft, hright] at hcontract
  exact hcontract

/-- Equivalent gain form: the channel entropy gain pays the full
`1-rho²` fraction of the uncontracted symmetric entropy drop. -/
theorem radialNatEntropy_gain_ge_topS_mul_drop
    {rho r z : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    topS rho * (Real.binEntropy z - radialNatEntropy 1 r z) ≤
      radialNatEntropy rho r z - radialNatEntropy 1 r z := by
  have hcontract := radialNatEntropyDrop_quadratic_contraction hrho hr hz
  unfold topS topR
  linarith

end CourtadeKumar
