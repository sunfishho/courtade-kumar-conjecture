import InformationTheory.CourtadeKumar.LowerRayTheorem

/-! Reduction of the single-ray LR interface to its three-variable scalar core. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- The scalar contact inequality after eliminating the multiplier, profile,
affine tangent, displacement, and entropy threshold from the single-ray
geometry record. -/
def SingleRayScalarContactTheorem (alpha : ℝ≥0) : Prop :=
  ∀ (M r z : ℝ),
    M ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    r ∈ Ioo (0 : ℝ) 1 →
    z ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) →
    M / z * radialTriangleEntropy r z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + r))) / 2 →
    bellmanEnvelope (alpha : ℝ) M ≤
      M / z * radialTriangleChannelEntropy alpha r z

/-- The canonical geometry hypotheses reduce LR exactly to the scalar
contact theorem. -/
theorem singleRayLR_of_scalarContact
    (alpha : ℝ≥0) (hscalar : SingleRayScalarContactTheorem alpha) :
    SingleRayLRTheorem alpha := by
  intro M d E0 h
  have hminus : M - d = M * (1 - h.r) := by
    linarith [h.moment_contact]
  have hplus : M + d = M * (1 + h.r) := by
    linarith [h.moment_contact]
  have hcontact : M / h.z * radialTriangleEntropy h.r h.z =
      (bellmanEnvelope (alpha : ℝ) (M * (1 - h.r)) +
        bellmanEnvelope (alpha : ℝ) (M * (1 + h.r))) / 2 := by
    calc
      M / h.z * radialTriangleEntropy h.r h.z = E0 :=
        h.entropy_contact.symm
      _ = (bellmanEnvelope (alpha : ℝ) (M - d) +
          bellmanEnvelope (alpha : ℝ) (M + d)) / 2 := h.threshold_eq
      _ = (bellmanEnvelope (alpha : ℝ) (M * (1 - h.r)) +
          bellmanEnvelope (alpha : ℝ) (M * (1 + h.r))) / 2 := by
        rw [hminus, hplus]
  exact hscalar M h.r h.z h.mean_interior h.ray_interior
    h.contact_before_half hcontact

end CourtadeKumar
