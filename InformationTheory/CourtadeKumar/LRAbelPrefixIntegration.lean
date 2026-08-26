import InformationTheory.CourtadeKumar.LRAbelPrefixDerivativeBound

/-! Integration of the audited Abel-prefix derivative estimate. -/

open Set

namespace CourtadeKumar

noncomputable def lrAbelPrefixAdjusted (N : ℕ) (v : ℝ) : ℝ :=
  lrAbelPrefixS N v -
    v ^ (2 * N + 1) / (4 * (N : ℝ) * (2 * (N : ℝ) + 1))

theorem hasDerivAt_lrAbelPrefixAdjusted
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (lrAbelPrefixAdjusted N)
      (lrAbelPrefixSDeriv N v - v ^ (2 * N) / (4 * (N : ℝ))) v := by
  have hNOne : 1 ≤ N := by omega
  have hNReal : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNOne)
  have hodd : 0 < 2 * (N : ℝ) + 1 := by positivity
  have hpow := (hasDerivAt_pow (2 * N + 1) v).div_const
    (4 * (N : ℝ) * (2 * (N : ℝ) + 1))
  have h := (hasDerivAt_lrAbelPrefixS hNOne hv).sub hpow
  convert h using 1
  rw [show 2 * N + 1 - 1 = 2 * N by omega]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hNReal.ne', hodd.ne']
  ring

theorem lrAbelPrefixAdjusted_antitone_segment
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn (lrAbelPrefixAdjusted N) (Icc v 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
  · intro y hy
    have hyv : v ≤ y := hy.1
    exact (hasDerivAt_lrAbelPrefixAdjusted hN (lt_of_lt_of_le hv.1 hyv)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_lrAbelPrefixAdjusted hN
      (lt_trans hv.1 hy.1)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    have hyPhysical : y ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hv.1 hy.1, hy.2⟩
    rw [(hasDerivAt_lrAbelPrefixAdjusted hN hyPhysical.1).deriv]
    linarith [lrAbelPrefixSDeriv_le hN hyPhysical]

/-- Integrating from `v` to one reduces prefix positivity to the single
endpoint estimate at `v = 1`. -/
theorem lrAbelPrefixS_lower_of_endpoint
    {N : ℕ} (hN : 2 ≤ N)
    (hend : 1 / (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) ≤
      lrAbelPrefixS N 1)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    v ^ (2 * N + 1) / (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) ≤
      lrAbelPrefixS N v := by
  have hanti := lrAbelPrefixAdjusted_antitone_segment hN hv
  have hcomp := hanti (show v ∈ Icc v (1 : ℝ) by exact ⟨le_rfl, hv.2.le⟩)
    (show (1 : ℝ) ∈ Icc v 1 by exact ⟨hv.2.le, le_rfl⟩) hv.2.le
  unfold lrAbelPrefixAdjusted at hcomp
  have hone :
      (1 : ℝ) ^ (2 * N + 1) /
          (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) =
        1 / (4 * (N : ℝ) * (2 * (N : ℝ) + 1)) := by simp
  rw [hone] at hcomp
  linarith

end CourtadeKumar
