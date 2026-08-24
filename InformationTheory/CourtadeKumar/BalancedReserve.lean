import InformationTheory.CourtadeKumar.EnvelopeFormula

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

/-! Algebraic core of the corrected balanced-root reserve. -/

/-! Natural-unit scalar functions used by the corrected centered-endpoint theorem. -/

noncomputable def topPhi (x : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy ((1 - x) / 2)

@[simp] lemma topPhi_one : topPhi 1 = Real.log 2 := by simp [topPhi]

@[simp] lemma topPhi_neg_one : topPhi (-1) = Real.log 2 := by simp [topPhi]

@[simp] lemma topPhi_zero : topPhi 0 = 0 := by
  rw [topPhi, show ((1 - (0 : ℝ)) / 2) = (2 : ℝ)⁻¹ by norm_num,
    Real.binEntropy_two_inv]
  ring

noncomputable def topJ (x : ℝ) : ℝ := Real.log 2 - topPhi x

@[simp] lemma topJ_neg (x : ℝ) : topJ (-x) = topJ x := by
  unfold topJ topPhi
  rw [show (1 - -x) / 2 = 1 - (1 - x) / 2 by ring,
    Real.binEntropy_one_sub]

noncomputable def topR (rho : ℝ) : ℝ := rho ^ 2

noncomputable def topS (rho : ℝ) : ℝ := 1 - topR rho

noncomputable def topEll (rho : ℝ) : ℝ :=
  topR rho * Real.log 2 - topPhi rho

noncomputable def topEnvelope (rho x : ℝ) : ℝ :=
  topS rho * topJ x + topEll rho * (1 - x ^ 2)

/-- The balanced contact residual `G(c,r)`. -/
noncomputable def balancedResidual (rho c r : ℝ) : ℝ :=
  c * topJ r - topS rho * topJ (c * r) -
    topEll rho * (1 - c ^ 2 * r ^ 2)

/-- The corrected balanced identity.  In particular, the final quadratic
term on the right is negative. -/
theorem correctedBalancedIdentity
    (rho c r : ℝ) (hbalanced : balancedResidual rho c r = 0) :
    c * Real.log 2 - topJ rho =
      c * topPhi r - topS rho * topPhi (c * r) -
        topEll rho * c ^ 2 * r ^ 2 := by
  unfold balancedResidual at hbalanced
  unfold topJ topS topR topEll at hbalanced ⊢
  unfold topR at hbalanced ⊢
  linear_combination hbalanced

noncomputable def topEnergy (rho z : ℝ) : ℝ :=
  topR rho * topPhi z - topPhi (rho * z)

noncomputable def topPerspectiveTerm (c r : ℝ) : ℝ :=
  c / 2 * topPhi r - (2 - c) / 2 * topPhi (c * r / (2 - c))

/-- The reserve after moving a centered contact to the endpoint. -/
noncomputable def topReserve (rho c r : ℝ) : ℝ :=
  topS rho * topPerspectiveTerm c r + c * topEnergy rho r -
    topEll rho * c ^ 2 * r ^ 2

noncomputable def balancedJunction (c r : ℝ) : ℝ :=
  c / 2 * topPhi r + (2 - c) / 2 * topPhi (c * r / (2 - c)) -
    topPhi (c * r)

/-- The balanced-root expression used for the endpoint certificate. -/
noncomputable def balancedReserve (rho c r : ℝ) : ℝ :=
  c * topJ (rho * r) - topJ rho - topS rho * balancedJunction c r

/-- At a balanced contact, the full TOP reserve is exactly the balanced
root expression.  This algebraic bridge depends on the corrected sign. -/
theorem topReserve_eq_balancedReserve
    (rho c r : ℝ) (hbalanced : balancedResidual rho c r = 0) :
    topReserve rho c r = balancedReserve rho c r := by
  have hcorrected := correctedBalancedIdentity rho c r hbalanced
  unfold topReserve topPerspectiveTerm topEnergy balancedReserve balancedJunction
  unfold topJ topS topR topEll at hcorrected ⊢
  unfold topR at hcorrected ⊢
  linear_combination -hcorrected

end CourtadeKumar
