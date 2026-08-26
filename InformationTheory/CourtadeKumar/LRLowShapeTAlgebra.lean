import InformationTheory.CourtadeKumar.LRLowShapeUReserve

/-!
# Algebraic reduction of the low-shape tangent reserve

This file identifies the midpoint numerator with the analytic `V` reserve
and verifies the normalized determinant identity used by certificate `(T)`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowYTangent (R v t : ℝ) : ℝ :=
  lrFlowPW R v t -
    4 * lrWKernel R 1 * lrFlowM v * t ^ 2

noncomputable def lrLowVReserve (R v t : ℝ) : ℝ :=
  lrFlowD R v t * lrFlowC R v t +
    lrFlowB R v t * lrLowYTangent R v t

noncomputable def lrLowHalfSlopeBase (v : ℝ) : ℝ :=
  -Real.log (1 - lrFlowM v / 2) / (lrFlowM v / 2) ^ 2

noncomputable def lrLowTDeterminant (R v t : ℝ) : ℝ :=
  4 * (lrWKernel R 1 / (1 - R) ^ 2) * lrFlowJ R v t *
      (lrFlowGap R v t / (1 - R)) +
    (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1) *
      (lrLowVReserve R v t / (1 - R) ^ 2)

lemma lrFlowNumeratorP_midpoint_eq_lrLowVReserve
    {R v t : ℝ} (hv : v ≠ -1) :
    lrFlowNumeratorP R (lrFlowM v) v t =
      lrLowVReserve R v t := by
  unfold lrFlowNumeratorP lrLowVReserve lrLowYTangent lrFlowC
    lrFlowD lrFlowA lrFlowM
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  field_simp [hden]
  ring

lemma lrFlowHalfSlope_eq_normalized
    {R v : ℝ} (hR : R ≠ 1) :
    lrFlowHalfSlope R v =
      (1 - R) *
        (lrLowHalfSlopeBase v + 4 * lrNormalizedEnergy R 1) := by
  have hden : 1 - R ≠ 0 := sub_ne_zero.mpr hR.symm
  have henergy :
      (1 - R) * lrNormalizedEnergy R 1 =
        R * Real.log 2 - topPhi (Real.sqrt R) := by
    unfold lrNormalizedEnergy
    rw [topPhi_one]
    field_simp [hden]
  unfold lrFlowHalfSlope lrFlowEllDeriv lrLowHalfSlopeBase
  rw [mul_add,
    show (1 - R) * (4 * lrNormalizedEnergy R 1) =
        4 * ((1 - R) * lrNormalizedEnergy R 1) by ring,
    henergy]
  ring

theorem lrFlowTReserve_eq_cube_mul_lrLowTDeterminant
    {R v t : ℝ} (hR : R ≠ 1) (hv : v ≠ -1) :
    lrFlowTReserve R v t =
      (1 - R) ^ 3 * lrLowTDeterminant R v t := by
  unfold lrFlowTReserve
  rw [lrFlowNumeratorP_midpoint_eq_lrLowVReserve hv,
    lrFlowHalfSlope_eq_normalized hR]
  unfold lrLowTDeterminant
  have hden : 1 - R ≠ 0 := sub_ne_zero.mpr hR.symm
  field_simp [hden]

theorem lrFlowTReserve_nonneg_of_lrLowTDeterminant_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) (hv : v ≠ -1)
    (hdet : 0 ≤ lrLowTDeterminant R v t) :
    0 ≤ lrFlowTReserve R v t := by
  rw [lrFlowTReserve_eq_cube_mul_lrLowTDeterminant hR.2.ne hv]
  exact mul_nonneg (pow_nonneg (sub_pos.mpr hR.2).le 3) hdet

end CourtadeKumar
