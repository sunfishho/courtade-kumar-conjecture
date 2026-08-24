import InformationTheory.CourtadeKumar.CanonicalRadialProfileSecondDerivative
import InformationTheory.CourtadeKumar.RadialContactShape
import Mathlib.Analysis.Convex.Deriv

/-! Strict convexity of the canonical profile after the centered contact. -/

open Set
open scoped NNReal

namespace CourtadeKumar

theorem natEntropySlope_one_sub (q : ℝ) :
    natEntropySlope (1 - q) = -natEntropySlope q := by
  unfold natEntropySlope
  ring_nf

theorem scaledNatEntropy_m_gradient_centered (c r : ℝ) :
    scaledNatEntropyDirectionalFirst c (1 / 2) (r * (1 / 2)) 1 0 0 = 0 := by
  unfold scaledNatEntropyDirectionalFirst
  simp only [mul_zero, sub_zero, add_zero, zero_mul, add_zero]
  rw [show (1 / 2 : ℝ) + c * (r * (1 / 2)) =
      1 - ((1 / 2 : ℝ) - c * (r * (1 / 2))) by ring]
  rw [natEntropySlope_one_sub]
  ring

theorem naturalTriangleKm_centered (rho theta r : ℝ) :
    naturalTriangleKm rho theta (1 / 2) (r * (1 / 2)) = 0 := by
  unfold naturalTriangleKm naturalTriangleDirectionalFirst
  rw [scaledNatEntropy_m_gradient_centered,
    scaledNatEntropy_m_gradient_centered]
  ring

/-- On the lower-contact branch, the derivative of the canonical profile is
strictly increasing. -/
theorem strictMonoOn_deriv_canonicalRadialProfile_after_threshold
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    StrictMonoOn
      (deriv (canonicalRadialProfile alpha theta halpha htheta))
      (Ioo rstar 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo rstar 1)
  · intro r hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hrstar.1.trans hr.1, hr.2⟩
    exact (hasDerivAt_deriv_canonicalRadialProfile
      halpha htheta hr01).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hrstar.1.trans hr.1, hr.2⟩
    exact deriv_deriv_canonicalRadialProfile_pos halpha htheta hr01
      (canonicalRadialContactZ_lt_half_after_threshold
        halpha htheta hrstar hcenter hr01 hr.1)

theorem strictConvexOn_canonicalRadialProfile_after_threshold
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    StrictConvexOn ℝ (Ico rstar 1)
      (canonicalRadialProfile alpha theta halpha htheta) := by
  have hmono := strictMonoOn_deriv_canonicalRadialProfile_after_threshold
    halpha htheta hrstar hcenter
  have hmono' : StrictMonoOn
      (deriv (canonicalRadialProfile alpha theta halpha htheta))
      (interior (Ico rstar 1)) := by
    simpa only [interior_Ico] using hmono
  apply hmono'.strictConvexOn_of_deriv (convex_Ico rstar 1)
  intro r hr
  have hr01 : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨hrstar.1.trans_le hr.1, hr.2⟩
  exact (hasDerivAt_canonicalRadialProfile
    halpha htheta hr01).continuousAt.continuousWithinAt

/-- At the centered contact, the profile tangent passes through the origin. -/
theorem canonicalRadialProfile_centered_tangent
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    canonicalRadialProfile alpha theta halpha htheta rstar =
      rstar * deriv (canonicalRadialProfile alpha theta halpha htheta) rstar := by
  let rho : ℝ := channelRho (alpha : ℝ)
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    dsimp [rho]
    exact channelRho_mem_Icc_of_alpha_interior halpha
  have hz : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) (1 + rstar)⁻¹ := by
    constructor
    · norm_num
    · rw [inv_eq_one_div, lt_div_iff₀ (by linarith [hrstar.1])]
      nlinarith [hrstar.2]
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hrstar hz
  have hratio : radialEulerRatio rho rstar (1 / 2) = theta := by
    rw [radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus]
    exact hcenter
  have hstat : theta * radialEulerDefect 1 rstar (1 / 2) -
      radialEulerDefect rho rstar (1 / 2) = 0 :=
    (radial_stationary_iff_ratio hminus hplus).2 hratio
  have hstationary := naturalTriangleLagrangian_euler_at_stationary hstat
  have hzcanonical := canonicalRadialContactZ_eq_half_of_centeredRoot
    halpha htheta hrstar hcenter
  rw [(hasDerivAt_canonicalRadialProfile halpha htheta hrstar).deriv]
  rw [canonicalRadialProfile, if_pos hrstar.1, hzcanonical]
  rw [radialTriangleDifference_eq_nat]
  rw [← naturalTriangleLagrangian_radial_eq]
  dsimp [rho] at hstationary ⊢
  rw [hstationary, naturalTriangleKm_centered]
  field_simp [log_two_ne_zero]
  ring

end CourtadeKumar
