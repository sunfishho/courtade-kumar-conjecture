import InformationTheory.CourtadeKumar.LRAbelLiftAssembly

/-! Closure of the audited LR sign charts using the analytic inequalities. -/

open Set

namespace CourtadeKumar

/-- On the regular physical interior, the corrected Abel lift closes the
`J = 0` chart: there the numerator is `B * Z`, with both factors nonnegative. -/
theorem lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : lrFlowJ R v t = 0) :
    0 ≤ lrFlowNumeratorP R p v t := by
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hvt : v * t < 1 := by
    nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
      mul_lt_mul_of_pos_left ht.2 hv.1]
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  exact lrFlowNumeratorP_nonneg_of_J_eq_zero
    (by linarith [hv.1])
    (lrFlowB_pos hv.1 ht.1.le hshape).le hJ
    (lrFlow_noise_lift_nonneg hR hv ht)

end CourtadeKumar
