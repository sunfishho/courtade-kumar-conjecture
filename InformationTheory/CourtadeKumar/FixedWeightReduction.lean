import InformationTheory.CourtadeKumar.BalancedReserve

/-! Exact fixed-weight decomposition for the corrected TOP theorem. -/

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

/-- The contact residual at fixed balanced weight `(c,r)`. -/
noncomputable def topContactResidual (rho c r X : ℝ) : ℝ :=
  c * topJ r -
    (topEnvelope rho (X + c * r) + topEnvelope rho (X - c * r)) / 2

/-- Symmetric entropy drop around `X` with half-width `b`. -/
noncomputable def topEntropyDrop (X b : ℝ) : ℝ :=
  topJ X - (topJ (X + b) + topJ (X - b)) / 2

/-- Auxiliary reserve whose value at an actual contact is the target gap. -/
noncomputable def topAuxiliaryReserve (rho c r Y : ℝ) : ℝ :=
  c * (topJ (rho * r) - topJ r) -
    topS rho * topEntropyDrop Y (c * r) -
      topEll rho * c ^ 2 * r ^ 2

/-- Exact fixed-weight decomposition of the centered TOP gap. -/
theorem topGap_eq_auxiliary_add_contactResidual (rho c r Y : ℝ) :
    c * topJ (rho * r) - topEnvelope rho Y =
      topAuxiliaryReserve rho c r Y + topContactResidual rho c r Y := by
  unfold topAuxiliaryReserve topContactResidual topEntropyDrop topEnvelope
  ring

/-- On the contact surface, the target gap is exactly the auxiliary reserve. -/
theorem topGap_eq_auxiliaryReserve_of_contact
    (rho c r X : ℝ) (hcontact : topContactResidual rho c r X = 0) :
    c * topJ (rho * r) - topEnvelope rho X =
      topAuxiliaryReserve rho c r X := by
  rw [topGap_eq_auxiliary_add_contactResidual, hcontact, add_zero]

/-- The contact residual at the centered point is the balanced residual. -/
lemma topContactResidual_zero (rho c r : ℝ) :
    topContactResidual rho c r 0 = balancedResidual rho c r := by
  unfold topContactResidual balancedResidual topEnvelope
  rw [show 0 + c * r = c * r by ring, show 0 - c * r = -(c * r) by ring]
  rw [topJ_neg]
  ring

end CourtadeKumar
