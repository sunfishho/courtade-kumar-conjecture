import InformationTheory.CourtadeKumar.LRRootVelocity

/-! Exact algebra of the three sign charts in the audited LR flow. -/

namespace CourtadeKumar

noncomputable def lrFlowM (v : ℝ) : ℝ := v / (1 + v)

noncomputable def lrFlowJ (R v t : ℝ) : ℝ :=
  lrFlowB R v t * t ^ 2 - lrFlowD R v t

noncomputable def lrFlowH (R v t : ℝ) : ℝ :=
  lrFlowD R v t - t ^ 2 * lrFlowB R v t

noncomputable def lrFlowQWeight (v t : ℝ) : ℝ :=
  (1 - v) + (1 + v) / 2 * (1 - t ^ 2)

noncomputable def lrFlowC (R v t : ℝ) : ℝ :=
  lrGShape t v + lrFlowPW R v t -
    4 * lrWKernel R 1 / (1 + v)

noncomputable def lrFlowZ (R v t : ℝ) : ℝ :=
  t ^ 2 * lrGShape t v +
    (1 + t ^ 2) * lrFlowPW R v t -
      4 * lrWKernel R 1 * t ^ 2

noncomputable def lrFlowNumeratorP (R p v t : ℝ) : ℝ :=
  lrFlowD R v t * lrGShape t v +
    lrFlowA v t * lrFlowPW R v t -
      4 * lrWKernel R 1 *
        ((1 - p) * lrFlowD R v t +
          p * t ^ 2 * lrFlowB R v t)

lemma lrFlowNumerator_eq_p (R u v t : ℝ) :
    lrFlowNumerator R u v t =
      lrFlowNumeratorP R (lrFlowP u) v t := by
  rfl

lemma lrFlowH_eq_negJ (R v t : ℝ) :
    lrFlowH R v t = -lrFlowJ R v t := by
  unfold lrFlowH lrFlowJ
  ring

/-- Equation (lr-negative-N) at the outer midpoint. -/
theorem lrFlowNumeratorP_midpoint
    {R v t : ℝ} (hv : v ≠ -1) :
    lrFlowNumeratorP R (lrFlowM v) v t =
      lrFlowB R v t * lrFlowZ R v t +
        lrFlowH R v t * lrFlowC R v t := by
  unfold lrFlowNumeratorP lrFlowZ lrFlowH lrFlowC
    lrFlowD lrFlowA lrFlowM
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  field_simp [hden]
  ring

/-- The flow numerator is affine in the input probability, with slope
`4 W H`. -/
theorem lrFlowNumeratorP_sub
    (R p₁ p₂ v t : ℝ) :
    lrFlowNumeratorP R p₂ v t - lrFlowNumeratorP R p₁ v t =
      4 * lrWKernel R 1 * lrFlowH R v t * (p₂ - p₁) := by
  unfold lrFlowNumeratorP lrFlowH
  ring

/-- Equation (lr-J-zero-collapse). -/
theorem lrFlowNumeratorP_of_J_eq_zero
    {R p v t : ℝ} (hv : v ≠ -1)
    (hJ : lrFlowJ R v t = 0) :
    lrFlowNumeratorP R p v t =
      lrFlowB R v t * lrFlowZ R v t := by
  have hH : lrFlowH R v t = 0 := by
    rw [lrFlowH_eq_negJ, hJ]
    simp
  have hmid := lrFlowNumeratorP_midpoint (R := R) (v := v) (t := t) hv
  have hsub := lrFlowNumeratorP_sub R (lrFlowM v) p v t
  simp only [hH, mul_zero, zero_mul, add_zero] at hmid hsub
  linarith

theorem lrFlowNumeratorP_nonneg_of_J_eq_zero
    {R p v t : ℝ} (hv : v ≠ -1)
    (hB : 0 ≤ lrFlowB R v t)
    (hJ : lrFlowJ R v t = 0)
    (hAbel : 0 ≤ lrFlowZ R v t +
      lrFlowQWeight v t * lrFlowH R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  have hH : lrFlowH R v t = 0 := by
    rw [lrFlowH_eq_negJ, hJ]
    simp
  have hZ : 0 ≤ lrFlowZ R v t := by simpa [hH] using hAbel
  rw [lrFlowNumeratorP_of_J_eq_zero hv hJ]
  exact mul_nonneg hB hZ

noncomputable def lrFlowX₀ (R v t : ℝ) : ℝ :=
  lrFlowC R v t - 2 * lrWKernel R 1 * lrFlowM v

noncomputable def lrFlowY₀ (R v t : ℝ) : ℝ :=
  lrFlowPW R v t -
    2 * lrWKernel R 1 * lrFlowM v * t ^ 2

/-- First identity in (lr-midpoint-identity). -/
theorem lrFlowNumeratorP_halfMidpoint
    {R v t : ℝ} (hv : v ≠ -1) :
    lrFlowNumeratorP R (lrFlowM v / 2) v t =
      lrFlowD R v t * lrFlowX₀ R v t +
        lrFlowB R v t * lrFlowY₀ R v t := by
  unfold lrFlowNumeratorP lrFlowX₀ lrFlowY₀ lrFlowC
    lrFlowD lrFlowA lrFlowM
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  field_simp [hden]
  ring

/-- Second identity in (lr-midpoint-identity). -/
theorem lrFlowY₀_add_t_sq_mul_X₀
    {R v t : ℝ} (hv : v ≠ -1) :
    lrFlowY₀ R v t + t ^ 2 * lrFlowX₀ R v t =
      lrFlowZ R v t := by
  unfold lrFlowY₀ lrFlowX₀ lrFlowZ lrFlowC lrFlowM
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linear_combination h
  field_simp [hden]
  ring

end CourtadeKumar
