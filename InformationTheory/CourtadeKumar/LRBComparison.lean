import InformationTheory.CourtadeKumar.LRWZSeries
import InformationTheory.CourtadeKumar.LRScalarEndpoint
import InformationTheory.CourtadeKumar.BalancedRoot
import InformationTheory.CourtadeKumar.LRFlowCharts

/-! Analytic quantities in the audited LR `B` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrBDelta (R : ℝ) : ℝ :=
  Real.log 2 - topPhi (Real.sqrt R)

noncomputable def lrBGamma (R : ℝ) : ℝ :=
  (1 - R) * Real.artanh (Real.sqrt R) /
    (2 * Real.sqrt R * lrBDelta R)

noncomputable def lrBKernelK (R y : ℝ) : ℝ :=
  (1 + R) / (2 * Real.sqrt R) *
      (Real.artanh (Real.sqrt R * y) / y) +
    (1 - R) / (2 * (1 - R * y ^ 2))

/-- The scalar reserve in equation `(lr-scalar-K)`. -/
noncomputable def lrBScalarReserve (R y : ℝ) : ℝ :=
  lrBGamma R * lrBKernelK R y - lrL (Real.sqrt R * y) +
    R * y ^ 2 * (1 - y ^ 2) / (2 * (1 - R * y ^ 2)) -
    Real.log 2

/-- The two-variable reserve whose nonnegativity is exactly the audited
`B` comparison. -/
noncomputable def lrBComparisonReserve (R v t : ℝ) : ℝ :=
  lrBGamma R * lrFlowC R v t -
    lrFlowB R v t * lrFlowQWeight v t

lemma lrB_sqrt_mem_Ioo {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt R ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨Real.sqrt_pos.2 hR.1,
    by simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2⟩

theorem lrBDelta_pos {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 < lrBDelta R := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  simpa [lrBDelta, topJ] using
    (topJ_pos (show Real.sqrt R ∈ Ioo (-1 : ℝ) 1 from
      ⟨by linarith [hsqrt.1], hsqrt.2⟩))

theorem lrBGamma_pos {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 < lrBGamma R := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hartanh : 0 < Real.artanh (Real.sqrt R) :=
    Real.artanh_pos hsqrt
  unfold lrBGamma
  exact div_pos (mul_pos (sub_pos.mpr hR.2) hartanh)
    (mul_pos (mul_pos (by norm_num) hsqrt.1) (lrBDelta_pos hR))

/-- The exact normalization identity `W = D_R (1 - gamma_R)`. -/
theorem lrWKernel_one_eq_delta_mul_one_sub_gamma
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrWKernel R 1 = lrBDelta R * (1 - lrBGamma R) := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hdelta := lrBDelta_pos hR
  unfold lrWKernel lrBGamma
  simp only [topPhi_one, mul_one]
  rw [show Real.log 2 - topPhi (Real.sqrt R) = lrBDelta R by rfl]
  field_simp [hsqrt.1.ne', hdelta.ne']

theorem lrBGamma_le_one {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrBGamma R ≤ 1 := by
  have hW := lrWKernel_one_nonneg hR
  rw [lrWKernel_one_eq_delta_mul_one_sub_gamma hR] at hW
  exact sub_nonneg.mp
    (nonneg_of_mul_nonneg_right hW (lrBDelta_pos hR))

end CourtadeKumar
