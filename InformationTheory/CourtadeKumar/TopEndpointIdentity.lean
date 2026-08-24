import InformationTheory.CourtadeKumar.EntropyDropTransition

/-! Exact endpoint evaluation of the corrected TOP auxiliary reserve. -/

open scoped ENNReal NNReal BigOperators

namespace CourtadeKumar

private lemma binaryEntropy_split_identity
    (c u v q : ℝ)
    (huv : u + v = 1)
    (hq : (2 - c) * q = 1 - c * v)
    (hq' : (2 - c) * (1 - q) = 1 - c * u) :
    2 * Real.binEntropy (c / 2) + c * Real.binEntropy u +
        (2 - c) * Real.binEntropy q =
      2 * Real.binEntropy (1 / 2) + Real.binEntropy (c * u) +
        Real.binEntropy (c * v) := by
  have hv : v = 1 - u := by linarith
  subst v
  simp_rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show c / 2 = c * (1 / 2) by ring, Real.negMulLog_mul]
  rw [show 1 - c * (1 / 2) = (2 - c) * (1 / 2) by ring,
    Real.negMulLog_mul]
  rw [Real.negMulLog_mul c u, Real.negMulLog_mul c (1 - u)]
  rw [← hq, ← hq', Real.negMulLog_mul, Real.negMulLog_mul]
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by ring]
  ring

/-- Endpoint evaluation of the symmetric entropy drop. -/
theorem topEntropyDrop_endpoint_identity
    (c r : ℝ) (hc : c ≠ 2) :
    topEntropyDrop (1 - c) (c * r) =
      c / 2 * topPhi r + (2 - c) / 2 * topPhi (c * r / (2 - c)) := by
  let u : ℝ := (1 - r) / 2
  let v : ℝ := (1 + r) / 2
  let q : ℝ := (1 - c * v) / (2 - c)
  have huv : u + v = 1 := by dsimp [u, v]; ring
  have hden : 2 - c ≠ 0 := sub_ne_zero.mpr hc.symm
  have hq : (2 - c) * q = 1 - c * v := by
    dsimp [q]
    field_simp
  have hq' : (2 - c) * (1 - q) = 1 - c * u := by
    dsimp [q, u, v]
    field_simp
    ring
  have hsplit := binaryEntropy_split_identity c u v q huv hq hq'
  rw [topEntropyDrop, topJ_eq_binEntropy]
  rw [show (1 - (1 - c)) / 2 = c / 2 by ring]
  rw [topJ_eq_binEntropy, topJ_eq_binEntropy]
  rw [show (1 - (1 - c + c * r)) / 2 = c * u by dsimp [u]; ring]
  rw [show (1 - (1 - c - c * r)) / 2 = c * v by dsimp [v]; ring]
  unfold topPhi
  rw [show (1 - r) / 2 = u by rfl]
  rw [show (1 - c * r / (2 - c)) / 2 = q by
    dsimp [q, v]
    field_simp
    ring]
  rw [show Real.log 2 = Real.binEntropy (1 / 2) by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.binEntropy_two_inv]]
  linarith

/-- At the endpoint `Y = 1-c`, the auxiliary reserve is exactly the
explicit reserve used by the corrected TOP theorem. -/
theorem topAuxiliaryReserve_endpoint_eq_topReserve
    (rho c r : ℝ) (hc : c ≠ 2) :
    topAuxiliaryReserve rho c r (1 - c) = topReserve rho c r := by
  rw [topAuxiliaryReserve, topReserve, topPerspectiveTerm, topEnergy,
    topEntropyDrop_endpoint_identity c r hc]
  unfold topJ topS topR
  ring

/-- The target gap at any admissible contact is bounded below by the explicit
corrected reserve. -/
theorem topGap_ge_topReserve_of_contact
    {rho c r X : ℝ}
    (hs : 0 ≤ topS rho) (hcr : 0 ≤ c * r) (hc : c ≠ 2)
    (hX : X ∈ Set.Icc (0 : ℝ) (1 - c))
    (hdomain : ∀ Y ∈ Set.Icc (0 : ℝ) (1 - c),
      Y ∈ Set.Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Set.Ioo (-1 : ℝ) 1 ∧
          Y - c * r ∈ Set.Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    c * topJ (rho * r) - topEnvelope rho X ≥ topReserve rho c r := by
  calc
    c * topJ (rho * r) - topEnvelope rho X ≥
        topAuxiliaryReserve rho c r (1 - c) :=
      topGap_ge_endpointAuxiliaryReserve_of_contact hs hcr hX hdomain hcontact
    _ = topReserve rho c r := topAuxiliaryReserve_endpoint_eq_topReserve rho c r hc

/-- Nonnegativity of the explicit reserve proves the corrected TOP target at
the contact. -/
theorem correctedTopTarget_of_reserve_nonneg
    {rho c r X : ℝ}
    (hs : 0 ≤ topS rho) (hcr : 0 ≤ c * r) (hc : c ≠ 2)
    (hX : X ∈ Set.Icc (0 : ℝ) (1 - c))
    (hdomain : ∀ Y ∈ Set.Icc (0 : ℝ) (1 - c),
      Y ∈ Set.Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Set.Ioo (-1 : ℝ) 1 ∧
          Y - c * r ∈ Set.Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0)
    (hreserve : 0 ≤ topReserve rho c r) :
    topEnvelope rho X ≤ c * topJ (rho * r) := by
  have hgap := topGap_ge_topReserve_of_contact hs hcr hc hX hdomain hcontact
  linarith

end CourtadeKumar
