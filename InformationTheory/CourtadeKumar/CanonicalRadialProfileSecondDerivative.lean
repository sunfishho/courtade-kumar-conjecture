import InformationTheory.CourtadeKumar.NaturalTriangleSecondPath
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Positive second derivative of the canonical profile below the centered contact. -/

open Set
open Filter
open scoped NNReal

namespace CourtadeKumar

noncomputable def canonicalRadialProfileDerivativeValue
    (alpha : ℝ≥0) (theta : ℝ)
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) (r : ℝ) : ℝ :=
  naturalTriangleKu (channelRho (alpha : ℝ)) theta
    (canonicalRadialContactZ alpha theta halpha htheta r)
    (r * canonicalRadialContactZ alpha theta halpha htheta r) /
      Real.log 2

theorem canonicalRadialProfileDerivativeValue_eq_deriv
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    canonicalRadialProfileDerivativeValue alpha theta halpha htheta r =
      deriv (canonicalRadialProfile alpha theta halpha htheta) r := by
  exact (hasDerivAt_canonicalRadialProfile halpha htheta hr).deriv.symm

theorem canonicalRadialProfileDerivativeValue_eq_quotientFirstVariation
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    canonicalRadialProfileDerivativeValue alpha theta halpha htheta r =
      quotientFirstVariation
        (naturalTriangleRadialPathNumerator (channelRho (alpha : ℝ)) theta
          (canonicalRadialContactZ alpha theta halpha htheta) r)
        (naturalTriangleRadialPathFirst (channelRho (alpha : ℝ)) theta
          (canonicalRadialContactZ alpha theta halpha htheta)
          (deriv (canonicalRadialContactZ alpha theta halpha htheta)) r)
        (canonicalRadialContactZ alpha theta halpha htheta r)
        (deriv (canonicalRadialContactZ alpha theta halpha htheta) r) /
          Real.log 2 := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let zfun : ℝ → ℝ := canonicalRadialContactZ alpha theta halpha htheta
  let z : ℝ := zfun r
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
  have hq := stationaryQuotientFirstVariation_eq_ku
    (dz := deriv zfun r) hz.1.ne' hstationary
  unfold canonicalRadialProfileDerivativeValue
  dsimp [rho, zfun, z] at hq ⊢
  unfold naturalTriangleRadialPathNumerator naturalTriangleRadialPathFirst
  rw [hq]

/-- The explicit envelope-derivative function is differentiable, with second
variation given by the accelerated stationary quotient formula. -/
theorem hasDerivAt_canonicalRadialProfileDerivativeValue
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    let zfun := canonicalRadialContactZ alpha theta halpha htheta
    let dzfun := deriv zfun
    let ddz := deriv dzfun r
    HasDerivAt (canonicalRadialProfileDerivativeValue alpha theta halpha htheta)
      (acceleratedQuotientSecondVariation
        (naturalTriangleLagrangian (channelRho (alpha : ℝ)) theta
          (zfun r) (r * zfun r))
        (affinePathFirstVariation
          (naturalTriangleKm (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (naturalTriangleKu (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (zfun r) r (dzfun r) 1)
        (acceleratedPathSecondVariation
          (naturalTriangleKm (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (naturalTriangleKu (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (naturalTriangleKmm (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (naturalTriangleKmu (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (naturalTriangleKuu (channelRho (alpha : ℝ)) theta
            (zfun r) (r * zfun r))
          (zfun r) r (dzfun r) 1 ddz 0)
        (zfun r) (dzfun r) ddz / Real.log 2) r := by
  dsimp only
  let rho : ℝ := channelRho (alpha : ℝ)
  let zfun : ℝ → ℝ := canonicalRadialContactZ alpha theta halpha htheta
  let dzfun : ℝ → ℝ := deriv zfun
  let ddz : ℝ := deriv dzfun r
  have hzC2 := contDiffAt_canonicalRadialContactZ halpha htheta hr
  have hzderiv : HasDerivAt zfun (dzfun r) r := by
    exact (hzC2.differentiableAt two_ne_zero).hasDerivAt
  have hdzC1 : ContDiffAt ℝ (1 : WithTop ℕ∞) dzfun r := by
    exact hzC2.derivWithin (m := (1 : WithTop ℕ∞)) (by norm_num)
  have hdz : HasDerivAt dzfun ddz r := by
    exact (hdzC1.differentiableAt one_ne_zero).hasDerivAt
  have hrho : rho ∈ Icc (0 : ℝ) 1 := by
    dsimp [rho]
    exact channelRho_mem_Icc_of_alpha_interior halpha
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : zfun r ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := hzspec.1
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hr hz
  have hRminus' : zfun r - rho * (r * zfun r) ∈ Ioo (0 : ℝ) 1 := by
    convert hRminus using 1 <;> ring
  have hRplus' : zfun r + rho * (r * zfun r) ∈ Ioo (0 : ℝ) 1 := by
    convert hRplus using 1 <;> ring
  have hminus' : zfun r - r * zfun r ∈ Ioo (0 : ℝ) 1 := by
    convert hminus using 1 <;> ring
  have hplus' : zfun r + r * zfun r ∈ Ioo (0 : ℝ) 1 := by
    convert hplus using 1 <;> ring
  have hk := hasDerivAt_naturalTriangleRadialPathNumerator
    (rho := rho) (theta := theta) (dz := dzfun) hzderiv
    hRminus' hRplus' hminus' hplus'
  have hkfirst := hasDerivAt_naturalTriangleRadialPathFirst
    (rho := rho) (theta := theta) hzderiv hdz
    hRminus' hRplus' hminus' hplus'
  have hq := hasDerivAt_quotientFirstVariation
    (k := naturalTriangleRadialPathNumerator rho theta zfun)
    (kfirst := naturalTriangleRadialPathFirst rho theta zfun dzfun)
    (z := zfun) (zfirst := dzfun)
    hk hkfirst hzderiv hdz hz.1.ne'
  have hbits := hq.div_const (Real.log 2)
  have hlocal :
      canonicalRadialProfileDerivativeValue alpha theta halpha htheta =ᶠ[nhds r]
      (fun s ↦ quotientFirstVariation
        (naturalTriangleRadialPathNumerator rho theta zfun s)
        (naturalTriangleRadialPathFirst rho theta zfun dzfun s)
        (zfun s) (dzfun s) / Real.log 2) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    simpa [rho, zfun, dzfun] using
      canonicalRadialProfileDerivativeValue_eq_quotientFirstVariation
        halpha htheta hs
  have hfinal := hbits.congr_of_eventuallyEq hlocal
  simpa [rho, zfun, dzfun, ddz, naturalTriangleRadialPathNumerator,
    naturalTriangleRadialPathFirst] using hfinal

noncomputable def canonicalRadialProfileSecondVariationValue
    (alpha : ℝ≥0) (theta : ℝ)
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) (r : ℝ) : ℝ :=
  let zfun := canonicalRadialContactZ alpha theta halpha htheta
  let dzfun := deriv zfun
  let ddz := deriv dzfun r
  acceleratedQuotientSecondVariation
    (naturalTriangleLagrangian (channelRho (alpha : ℝ)) theta
      (zfun r) (r * zfun r))
    (affinePathFirstVariation
      (naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (naturalTriangleKu (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (zfun r) r (dzfun r) 1)
    (acceleratedPathSecondVariation
      (naturalTriangleKm (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (naturalTriangleKu (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (naturalTriangleKmm (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (naturalTriangleKmu (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (naturalTriangleKuu (channelRho (alpha : ℝ)) theta
        (zfun r) (r * zfun r))
      (zfun r) r (dzfun r) 1 ddz 0)
    (zfun r) (dzfun r) ddz / Real.log 2

theorem hasDerivAt_canonicalRadialProfileDerivativeValue_compact
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (canonicalRadialProfileDerivativeValue alpha theta halpha htheta)
      (canonicalRadialProfileSecondVariationValue alpha theta halpha htheta r) r := by
  simpa [canonicalRadialProfileSecondVariationValue] using
    hasDerivAt_canonicalRadialProfileDerivativeValue halpha htheta hr

/-- The second-variation value is strictly positive whenever the canonical
contact lies below `1/2`. -/
theorem canonicalRadialProfileSecondVariationValue_pos
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hzhalf : canonicalRadialContactZ alpha theta halpha htheta r < 1 / 2) :
    0 < canonicalRadialProfileSecondVariationValue
      alpha theta halpha htheta r := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let zfun : ℝ → ℝ := canonicalRadialContactZ alpha theta halpha htheta
  let z : ℝ := zfun r
  let dz : ℝ := deriv zfun r
  let ddz : ℝ := deriv (deriv zfun) r
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    unfold rho channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := hzspec.1
  have hrhoClosed : rho ∈ Icc (0 : ℝ) 1 := ⟨hrho.1.le, hrho.2.le⟩
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrhoClosed hr hz
  have hratio : radialEulerRatio rho r z = theta := by
    rw [radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus]
    exact hzspec.2
  have hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect rho r z = 0 :=
    (radial_stationary_iff_ratio hminus hplus).2 hratio
  have hstationary := naturalTriangleLagrangian_euler_at_stationary hstat
  have hpositive : ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 →
      0 < hessianQuadratic
        (naturalTriangleKmm rho theta z (r * z))
        (naturalTriangleKmu rho theta z (r * z))
        (naturalTriangleKuu rho theta z (r * z)) x y := by
    intro x y hxy
    rw [naturalTriangle_hessianQuadratic]
    rw [naturalTriangleDirectionalCurvature_radial]
    exact radialLagrangianDirectionalCurvature_pos hrho hr hz
      (by simpa [zfun, z] using hzhalf) hstat hxy
  have hacc : 0 < acceleratedQuotientSecondVariation
      (naturalTriangleLagrangian rho theta z (r * z))
      (affinePathFirstVariation
        (naturalTriangleKm rho theta z (r * z))
        (naturalTriangleKu rho theta z (r * z)) z r dz 1)
      (acceleratedPathSecondVariation
        (naturalTriangleKm rho theta z (r * z))
        (naturalTriangleKu rho theta z (r * z))
        (naturalTriangleKmm rho theta z (r * z))
        (naturalTriangleKmu rho theta z (r * z))
        (naturalTriangleKuu rho theta z (r * z))
        z r dz 1 ddz 0)
      z dz ddz :=
    acceleratedPerspectiveSecondVariation_pos hz.1 hstationary
      (Or.inr one_ne_zero) hpositive
  unfold canonicalRadialProfileSecondVariationValue
  dsimp [rho, zfun, z, dz, ddz] at hacc ⊢
  exact div_pos hacc (Real.log_pos one_lt_two)

theorem hasDerivAt_deriv_canonicalRadialProfile
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (canonicalRadialProfile alpha theta halpha htheta))
      (canonicalRadialProfileSecondVariationValue alpha theta halpha htheta r) r := by
  have hvalue := hasDerivAt_canonicalRadialProfileDerivativeValue_compact
    halpha htheta hr
  apply hvalue.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact (canonicalRadialProfileDerivativeValue_eq_deriv halpha htheta hs).symm

/-- The genuine second derivative of the canonical profile is positive on
the lower-contact branch. -/
theorem deriv_deriv_canonicalRadialProfile_pos
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hzhalf : canonicalRadialContactZ alpha theta halpha htheta r < 1 / 2) :
    0 < deriv (deriv (canonicalRadialProfile alpha theta halpha htheta)) r := by
  rw [(hasDerivAt_deriv_canonicalRadialProfile halpha htheta hr).deriv]
  exact canonicalRadialProfileSecondVariationValue_pos
    halpha htheta hr hzhalf

end CourtadeKumar
