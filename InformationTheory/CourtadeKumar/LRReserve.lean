import InformationTheory.CourtadeKumar.LROdds

/-! The exact `Q_rho - kappa` reserve in the audited target-root LR flow. -/

open Set

namespace CourtadeKumar

noncomputable def lrQClosed (rho u v t : ℝ) : ℝ :=
  1 / t ^ 2 * (topPhi (v * t) / v - topPhi (u * t) / u) +
    1 / (topS rho * t ^ 2) *
      (topEnergy rho t + topEnergy rho (v * t) / v)

noncomputable def lrKappa (rho u : ℝ) : ℝ :=
  lrMu rho * u / (1 + u)

noncomputable def lrReserve (rho u v t : ℝ) : ℝ :=
  lrQClosed rho u v t - lrKappa rho u

/-- The manuscript's exact contact-residual identity before any inequality
is applied. -/
theorem lr_contactResidual_eq_Q
    {rho u v t : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t)
    (hroot : lrGShape (rho * t) v = lrObjectiveTarget rho u) :
    lrGShape t v - lrEntropyTarget rho u t =
      -(topS rho) * t ^ 2 * (lrQClosed rho u v t - lrKappa rho u) := by
  have hs : topS rho ≠ 0 := by
    unfold topS topR
    nlinarith [hrho.1, hrho.2]
  have hs' : 1 - rho ^ 2 ≠ 0 := by
    simpa [topS, topR] using hs
  simp only [lrGShape, lrObjectiveTarget, lrEntropyTarget, lrQClosed,
    lrKappa, lrMu, topEnergy, topS, topR] at hroot ⊢
  field_simp [hu.ne', hv.ne', ht.ne', hs'] at hroot ⊢
  linear_combination u * hroot

theorem lr_contactResidual_eq_reserve
    {rho u v t : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t)
    (hroot : lrGShape (rho * t) v = lrObjectiveTarget rho u) :
    lrGShape t v - lrEntropyTarget rho u t =
      -(topS rho) * t ^ 2 * lrReserve rho u v t := by
  rw [lrReserve]
  exact lr_contactResidual_eq_Q hrho hu hv ht hroot

/-- Equation (lr-Q-equivalence), with every sign-bearing factor explicit. -/
theorem lr_contactAtTarget_iff_Q
    {rho u v t : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t)
    (hroot : lrGShape (rho * t) v = lrObjectiveTarget rho u) :
    lrGShape t v ≤ lrEntropyTarget rho u t ↔
      lrKappa rho u ≤ lrQClosed rho u v t := by
  have hs : 0 < topS rho := by
    unfold topS topR
    nlinarith [hrho.1, hrho.2]
  have hfactor : 0 < topS rho * t ^ 2 := mul_pos hs (sq_pos_of_pos ht)
  have hid := lr_contactResidual_eq_Q hrho hu hv ht hroot
  constructor
  · intro h
    have hresidual :
        lrGShape t v - lrEntropyTarget rho u t ≤ 0 := sub_nonpos.mpr h
    rw [hid] at hresidual
    nlinarith
  · intro h
    have hresidual :
        lrGShape t v - lrEntropyTarget rho u t ≤ 0 := by
      rw [hid]
      nlinarith
    exact sub_nonpos.mp hresidual

end CourtadeKumar
