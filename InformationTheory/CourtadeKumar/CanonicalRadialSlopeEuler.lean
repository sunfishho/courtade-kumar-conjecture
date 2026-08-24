import InformationTheory.CourtadeKumar.CanonicalRadialSlopeRight

/-! Euler representation of the canonical radial slope derivative. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- At every interior canonical contact, the numerator of `(c(r)/r)'` is
exactly the negative midpoint-gradient component, in bit units. -/
theorem radialProfileSlopeNumerator_eq_neg_Km
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    r * deriv (canonicalRadialProfile alpha theta halpha htheta) r -
        canonicalRadialProfile alpha theta halpha htheta r =
      -naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (r * canonicalRadialContactZ alpha theta halpha htheta r) /
          Real.log 2 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let z : ℝ := canonicalRadialContactZ alpha theta halpha htheta r
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    dsimp [rho]
    exact channelRho_mem_Icc_of_alpha_interior halpha
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := hzspec.1
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hr hz
  have hratio : radialEulerRatio rho r z = theta := by
    rw [radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus]
    exact hzspec.2
  have hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0 :=
    (radial_stationary_iff_ratio hminus hplus).2 hratio
  have hstationary := naturalTriangleLagrangian_euler_at_stationary hstat
  have hz0 : canonicalRadialContactZ alpha theta halpha htheta r ≠ 0 := by
    simpa [z] using hz.1.ne'
  rw [(hasDerivAt_canonicalRadialProfile halpha htheta hr).deriv]
  rw [canonicalRadialProfile, if_pos hr.1]
  rw [radialTriangleDifference_eq_nat]
  rw [← naturalTriangleLagrangian_radial_eq]
  dsimp [rho, z] at hstationary ⊢
  rw [hstationary]
  field_simp [log_two_ne_zero, hz0]
  ring

theorem deriv_radialProfileSlope_eq_neg_Km
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv (radialProfileSlope
      (canonicalRadialProfile alpha theta halpha htheta)) r =
      (-naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (r * canonicalRadialContactZ alpha theta halpha htheta r) /
          Real.log 2) / r ^ 2 := by
  have hc0 := hasDerivAt_canonicalRadialProfile halpha htheta hr
  have hc : HasDerivAt
      (canonicalRadialProfile alpha theta halpha htheta)
      (deriv (canonicalRadialProfile alpha theta halpha htheta) r) r :=
    hc0.congr_deriv hc0.deriv.symm
  rw [(hasDerivAt_radialProfileSlope hr.1.ne' hc).deriv]
  rw [radialProfileSlopeNumerator_eq_neg_Km halpha htheta hr]

theorem deriv_radialProfileSlope_neg_iff_Km_pos
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv (radialProfileSlope
        (canonicalRadialProfile alpha theta halpha htheta)) r < 0 ↔
      0 < naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (r * canonicalRadialContactZ alpha theta halpha htheta r) := by
  rw [deriv_radialProfileSlope_eq_neg_Km halpha htheta hr]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr.1
  constructor
  · intro h
    have hnum : -naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (r * canonicalRadialContactZ alpha theta halpha htheta r) /
          Real.log 2 < 0 := by
      by_contra hn
      exact (not_lt_of_ge (div_nonneg (le_of_not_gt hn) hr2.le)) h
    have hneg : -naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (r * canonicalRadialContactZ alpha theta halpha htheta r) < 0 := by
      by_contra hn
      exact (not_lt_of_ge (div_nonneg (le_of_not_gt hn) hlog.le)) hnum
    linarith
  · intro h
    exact div_neg_of_neg_of_pos
      (div_neg_of_neg_of_pos (by linarith) hlog) hr2

end CourtadeKumar
