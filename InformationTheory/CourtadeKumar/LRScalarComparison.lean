import InformationTheory.CourtadeKumar.LRBComparison
import Mathlib.Analysis.Convex.Deriv

/-! Elementary analytic reductions in the audited scalar `K` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrScalarEndpointUpper (z : ℝ) : ℝ :=
  z * (z ^ 2 + 12 * z + 12) / (6 * (z + 1) * (z + 2))

noncomputable def lrScalarEndpointLogGap (z : ℝ) : ℝ :=
  lrScalarEndpointUpper z - Real.log (1 + z)

theorem hasDerivAt_lrScalarEndpointLogGap
    {z : ℝ} (h1 : z ≠ -1) (h2 : z ≠ -2) :
    HasDerivAt lrScalarEndpointLogGap
      (z ^ 4 / (6 * (z + 1) ^ 2 * (z + 2) ^ 2)) z := by
  have hid := hasDerivAt_id z
  have hp : HasDerivAt (fun x : ℝ => x ^ 2 + 12 * x + 12)
      (2 * z + 12) z := by
    simpa [id_eq] using
      ((hid.pow 2).add (hid.const_mul 12)).add_const 12
  have hn : HasDerivAt (fun x : ℝ => x * (x ^ 2 + 12 * x + 12))
      ((z ^ 2 + 12 * z + 12) + z * (2 * z + 12)) z := by
    simpa [id_eq] using hid.mul hp
  have hd : HasDerivAt (fun x : ℝ => 6 * (x + 1) * (x + 2))
      (6 * (z + 2) + 6 * (z + 1)) z := by
    simpa [id_eq] using
      ((hid.add_const 1).const_mul 6).mul (hid.add_const 2)
  have hz1 : z + 1 ≠ 0 := by
    intro hz
    apply h1
    linarith
  have hz2 : z + 2 ≠ 0 := by
    intro hz
    apply h2
    linarith
  have hdne : 6 * (z + 1) * (z + 2) ≠ 0 := by positivity
  have hq := hn.div hd hdne
  have hz1' : 1 + z ≠ 0 := by simpa [add_comm] using hz1
  have hl : HasDerivAt (fun x : ℝ => Real.log (1 + x))
      (1 / (1 + z)) z := by
    simpa [id_eq, add_comm] using
      (hid.add_const 1).log (by simpa [id_eq, add_comm] using hz1)
  unfold lrScalarEndpointLogGap lrScalarEndpointUpper
  convert hq.sub hl using 1
  field_simp [hz1, hz1', hz2]
  ring

/-- The rational upper bound for `log (1+z)` used at the scalar endpoint. -/
theorem log_one_add_le_lrScalarEndpointUpper
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Real.log (1 + z) ≤ lrScalarEndpointUpper z := by
  have hmono : MonotoneOn lrScalarEndpointLogGap (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    · intro y hy
      exact (hasDerivAt_lrScalarEndpointLogGap
        (by linarith [hy.1]) (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_lrScalarEndpointLogGap
        (by linarith [hy.1]) (by linarith [hy.1])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hasDerivAt_lrScalarEndpointLogGap
        (by linarith [hy.1]) (by linarith [hy.1])).deriv]
      have hy1 : 0 < y + 1 := by linarith [hy.1]
      have hy2 : 0 < y + 2 := by linarith [hy.1]
      exact div_nonneg (pow_nonneg hy.1.le _)
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg (y + 1)))
          (sq_nonneg (y + 2)))
  have h := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hz hz.1
  simpa [lrScalarEndpointLogGap, lrScalarEndpointUpper] using h

noncomputable def lrScalarLogRatio (z : ℝ) : ℝ :=
  (1 - z) / (1 + z)

noncomputable def lrScalarLogLower (z : ℝ) : ℝ :=
  let r := lrScalarLogRatio z
  2 * (r + r ^ 3 / 3)

noncomputable def lrArtanhCubicGap (r : ℝ) : ℝ :=
  Real.artanh r - r - r ^ 3 / 3

theorem hasDerivAt_lrArtanhCubicGap
    {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt lrArtanhCubicGap (r ^ 4 / (1 - r ^ 2)) r := by
  have h := ((hasDerivAt_artanh hr).sub (hasDerivAt_id r)).sub
    ((hasDerivAt_id r).pow 3 |>.div_const 3)
  unfold lrArtanhCubicGap
  convert h using 1
  simp only [id_eq, Nat.cast_ofNat]
  have hden : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  field_simp [hden]
  ring

theorem artanh_cubic_lower
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    r + r ^ 3 / 3 ≤ Real.artanh r := by
  have hmono : MonotoneOn lrArtanhCubicGap (Icc (0 : ℝ) r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) r)
    · intro y hy
      have hyOpen : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hy.1], lt_of_le_of_lt hy.2 hr.2⟩
      exact (hasDerivAt_lrArtanhCubicGap hyOpen).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyOpen : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hy.1], lt_trans hy.2 hr.2⟩
      exact (hasDerivAt_lrArtanhCubicGap hyOpen).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyOpen : y ∈ Ioo (-1 : ℝ) 1 :=
        ⟨by linarith [hy.1], lt_trans hy.2 hr.2⟩
      rw [(hasDerivAt_lrArtanhCubicGap hyOpen).deriv]
      exact div_nonneg (pow_nonneg hy.1.le _)
        (by nlinarith [hyOpen.1, hyOpen.2] : 0 ≤ 1 - y ^ 2)
  have h := hmono (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.1⟩)
    (show r ∈ Icc 0 r from ⟨hr.1, le_rfl⟩) hr.1
  dsimp [lrArtanhCubicGap] at h
  simp only [Real.artanh_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    zero_div, sub_zero] at h
  linarith

lemma lrScalarLogRatio_mem_Ioo
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    lrScalarLogRatio z ∈ Ioo (0 : ℝ) 1 := by
  unfold lrScalarLogRatio
  constructor
  · exact div_pos (sub_pos.mpr hz.2) (by linarith [hz.1])
  · rw [div_lt_one (by linarith [hz.1])]
    linarith [hz.1]

lemma two_mul_artanh_lrScalarLogRatio
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    2 * Real.artanh (lrScalarLogRatio z) = -Real.log z := by
  have hr := lrScalarLogRatio_mem_Ioo hz
  rw [Real.artanh_eq_half_log ⟨by linarith [hr.1], hr.2.le⟩]
  have hratio :
      (1 + lrScalarLogRatio z) / (1 - lrScalarLogRatio z) = z⁻¹ := by
    unfold lrScalarLogRatio
    have hzp : 1 + z ≠ 0 := ne_of_gt (by linarith [hz.1])
    have hden : 1 - (1 - z) / (1 + z) ≠ 0 := by
      have hdenEq : 1 - (1 - z) / (1 + z) = 2 * z / (1 + z) := by
        field_simp [hzp]
        ring
      rw [hdenEq]
      exact div_ne_zero (mul_ne_zero (by norm_num) hz.1.ne') hzp
    field_simp [hz.1.ne', hzp, hden]
    ring
  rw [hratio, Real.log_inv]
  ring

/-- The cubic lower bound for `-log z` used in the elementary endpoint
certificate. -/
theorem lrScalarLogLower_le_neg_log
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    lrScalarLogLower z ≤ -Real.log z := by
  have hr := lrScalarLogRatio_mem_Ioo hz
  have h := artanh_cubic_lower
    (show lrScalarLogRatio z ∈ Ico (0 : ℝ) 1 from ⟨hr.1.le, hr.2⟩)
  rw [← two_mul_artanh_lrScalarLogRatio hz]
  unfold lrScalarLogLower
  dsimp only
  linarith

end CourtadeKumar
