import InformationTheory.CourtadeKumar.BalancedReserveClosure
import InformationTheory.CourtadeKumar.ReserveConcavity

/-! Closure of the corrected interior TOP theorem.

The transition-selector argument is not needed for the sign conclusion.
For fixed channel and ray, the corrected reserve is concave in the weight,
vanishes at weight zero, and is nonnegative at the balanced root.  Hence its
chord from zero to the balanced root is nonnegative.  Every actual contact
weight lies on this chord because the contact residual is monotone in its
center and the balanced residual is strictly increasing in the weight. -/

open Set

namespace CourtadeKumar

@[simp] theorem topReserve_zero_weight (rho r : ℝ) :
    topReserve rho 0 r = 0 := by
  simp [topReserve, topPerspectiveTerm]

/-- Concavity transports balanced-root positivity to every smaller
nonnegative weight. -/
theorem topReserve_nonneg_below_balancedRoot
    {rho r c cᵦ : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) cᵦ) (hcᵦ : cᵦ ∈ Ioo (0 : ℝ) 1)
    (hroot : balancedResidual rho cᵦ r = 0) :
    0 ≤ topReserve rho c r := by
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1.le, hrho.2.le⟩
  exact topReserve_nonneg_between hr.1.le hr.2.le
    (topS_nonneg hrhoIcc) (topEll_nonneg hrhoIcc)
    (by simp) ⟨hcᵦ.1.le, hcᵦ.2.le⟩ hc.1 hc.2
    (by simp) (topReserve_nonneg_at_balancedRoot hrho hr hcᵦ hroot)

/-- Every interior fixed-weight contact has weight at most the unique
balanced contact weight. -/
theorem contactWeight_le_balancedRoot
    {rho r c X U cᵦ : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hcᵦ : cᵦ ∈ Ioo (0 : ℝ) 1)
    (hX : X ∈ Icc (0 : ℝ) U)
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) U,
      Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0)
    (hroot : balancedResidual rho cᵦ r = 0) :
    c ≤ cᵦ := by
  have hrhoIcc : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1.le, hrho.2.le⟩
  have hresidual : balancedResidual rho c r ≤ 0 :=
    balancedResidual_nonpos_of_contact_channel hrhoIcc hX hdomain hcontact
  by_contra hle
  have hlt : cᵦ < c := lt_of_not_ge hle
  have hstrict := balancedResidual_strictMonoOn hrhoIcc hr
    (show cᵦ ∈ Icc (0 : ℝ) 1 from ⟨hcᵦ.1.le, hcᵦ.2.le⟩)
    (show c ∈ Icc (0 : ℝ) 1 from ⟨hc.1.le, hc.2.le⟩) hlt
  change balancedResidual rho cᵦ r < balancedResidual rho c r at hstrict
  rw [hroot] at hstrict
  linarith

/-- The corrected TOP inequality for all nondegenerate interior channel,
ray, weight, and contact parameters. -/
theorem correctedTopTarget_interior
    {rho c r X : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hX : X ∈ Icc (0 : ℝ) (1 - c))
    (hdomain : ∀ Y ∈ Icc (0 : ℝ) (1 - c),
      Y ∈ Ioo (-1 : ℝ) 1 ∧
        Y + c * r ∈ Ioo (-1 : ℝ) 1 ∧ Y - c * r ∈ Ioo (-1 : ℝ) 1)
    (hcontact : topContactResidual rho c r X = 0) :
    topEnvelope rho X ≤ c * topJ (rho * r) := by
  obtain ⟨cᵦ, ⟨hcᵦ, hroot⟩, _⟩ := existsUnique_balancedRoot hrho hr
  have hc_le : c ≤ cᵦ := contactWeight_le_balancedRoot hrho hr hc hcᵦ hX
    (fun Y hY ↦ ⟨(hdomain Y hY).2.1, (hdomain Y hY).2.2⟩) hcontact hroot
  have hreserve : 0 ≤ topReserve rho c r :=
    topReserve_nonneg_below_balancedRoot hrho hr ⟨hc.1.le, hc_le⟩ hcᵦ hroot
  exact correctedTopTarget_of_reserve_nonneg
    (topS_nonneg ⟨hrho.1.le, hrho.2.le⟩)
    (mul_nonneg hc.1.le hr.1.le) (by linarith [hc.2]) hX hdomain
    hcontact hreserve

end CourtadeKumar
