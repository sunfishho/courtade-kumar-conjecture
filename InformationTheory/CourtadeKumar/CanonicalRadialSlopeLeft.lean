import InformationTheory.CourtadeKumar.CanonicalRadialSlopeEuler
import InformationTheory.CourtadeKumar.RadialMidpointGradientSign

/-! Decrease of the canonical radial slope before the centered contact. -/

open Set
open scoped NNReal

namespace CourtadeKumar

theorem radialEulerLogRatio_eq_midpoint_log_ratio
    {rho r z : ℝ}
    (hlog1 : Real.log (radialEulerLogArg 1 r z) ≠ 0) :
    radialEulerLogRatio rho r z =
      Real.log (radialEulerLogArg rho r z) /
        Real.log (radialEulerLogArg 1 r z) := by
  unfold radialEulerLogRatio radialEulerLog
  field_simp [hlog1]

theorem naturalTriangleKm_canonical_pos_before_threshold
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo (0 : ℝ) rstar) :
    0 < naturalTriangleKm (channelRho (alpha : ℝ)) theta
      (canonicalRadialContactZ alpha theta halpha htheta r)
      (r * canonicalRadialContactZ alpha theta halpha htheta r) := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let z : ℝ := canonicalRadialContactZ alpha theta halpha htheta r
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hrstar.2⟩
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    unfold rho channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : z ∈ Ioo (1 / 2 : ℝ) (1 + r)⁻¹ := by
    exact ⟨canonicalRadialContactZ_gt_half_before_threshold
      halpha htheta hrstar hcenter hr01 hr.2, hzspec.1.2⟩
  have h1r : 0 < 1 + r := by linarith [hr.1]
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
      _ = 1 := inv_mul_cancel₀ h1r.ne'
  obtain ⟨harg1, _, _⟩ := radialEulerLogArg_order_physical
    (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
    hr.1 (lt_trans (by norm_num) hz.1) hupper
  have harg1lt1 : radialEulerLogArg 1 r z < 1 :=
    harg1.2.trans (by linarith [hz.1])
  have hlog1 : Real.log (radialEulerLogArg 1 r z) ≠ 0 :=
    (Real.log_neg harg1.1 harg1lt1).ne
  have hthetaLog : theta = Real.log (radialEulerLogArg rho r z) /
      Real.log (radialEulerLogArg 1 r z) := by
    rw [← hzspec.2]
    exact radialEulerLogRatio_eq_midpoint_log_ratio hlog1
  exact naturalTriangleKm_pos_of_log_ratio_stationary
    hrho hr01 hz hthetaLog

theorem deriv_radialProfileSlope_neg_before_threshold
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo (0 : ℝ) rstar) :
    deriv (radialProfileSlope
      (canonicalRadialProfile alpha theta halpha htheta)) r < 0 := by
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hrstar.2⟩
  rw [deriv_radialProfileSlope_neg_iff_Km_pos halpha htheta hr01]
  exact naturalTriangleKm_canonical_pos_before_threshold
    halpha htheta hrstar hcenter hr

theorem strictAntiOn_radialProfileSlope_before_threshold
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    StrictAntiOn (radialProfileSlope
      (canonicalRadialProfile alpha theta halpha htheta))
      (Ioc (0 : ℝ) rstar) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc (0 : ℝ) rstar)
  · intro r hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans_lt hrstar.2⟩
    exact (hasDerivAt_radialProfileSlope hr.1.ne'
      (hasDerivAt_canonicalRadialProfile halpha htheta hr01)).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioc] at hr
    exact deriv_radialProfileSlope_neg_before_threshold
      halpha htheta hrstar hcenter hr

end CourtadeKumar
