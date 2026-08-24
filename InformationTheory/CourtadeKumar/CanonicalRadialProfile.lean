import InformationTheory.CourtadeKumar.RadialEulerRoot

/-! Canonical radial contacts selected from the unique Euler roots. -/

open Set
open scoped NNReal

namespace CourtadeKumar

noncomputable def canonicalRadialContactZ
    (alpha : ℝ≥0) (theta : ℝ)
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) (r : ℝ) : ℝ :=
  if hr : 0 < r then
    Classical.choose (existsUnique_radialEulerLogRatio_eq
      (channelRho_mem_Ico_of_alpha_interior halpha) htheta hr)
  else 1

theorem canonicalRadialContactZ_spec
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) :
    canonicalRadialContactZ alpha theta halpha htheta r ∈
        Ioo (0 : ℝ) (1 + r)⁻¹ ∧
      radialEulerLogRatio (channelRho (alpha : ℝ)) r
        (canonicalRadialContactZ alpha theta halpha htheta r) = theta := by
  unfold canonicalRadialContactZ
  simp only [dif_pos hr]
  exact (Classical.choose_spec (existsUnique_radialEulerLogRatio_eq
    (channelRho_mem_Ico_of_alpha_interior halpha) htheta hr)).1

noncomputable def canonicalRadialProfile
    (alpha : ℝ≥0) (theta : ℝ)
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) (r : ℝ) : ℝ :=
  if 0 < r then
    radialTriangleDifference alpha theta r
      (canonicalRadialContactZ alpha theta halpha htheta r) /
        canonicalRadialContactZ alpha theta halpha htheta r
  else 0

@[simp] theorem canonicalRadialProfile_zero
    (alpha : ℝ≥0) (theta : ℝ)
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    canonicalRadialProfile alpha theta halpha htheta 0 = 0 := by
  simp [canonicalRadialProfile]

/-- The canonical root selection supplies the complete stationary-profile
data on every interior shape ray. -/
theorem canonicalRadialProfile_interiorStationary
    {alpha : ℝ≥0} {theta : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    RadialInteriorStationaryProfile alpha theta
      (canonicalRadialProfile alpha theta halpha htheta) := by
  intro r hr
  let z : ℝ := canonicalRadialContactZ alpha theta halpha htheta r
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := hzspec.1
  have hlogRatio : radialEulerLogRatio (channelRho (alpha : ℝ)) r z = theta :=
    hzspec.2
  have hrho : channelRho (alpha : ℝ) ∈ Icc (0 : ℝ) 1 :=
    channelRho_mem_Icc_of_alpha_interior halpha
  obtain ⟨hRminus, hRplus, hminus, hplus⟩ :=
    radialEntropyArgs_physical hrho hr hz
  have hratio : radialEulerRatio (channelRho (alpha : ℝ)) r z = theta := by
    rw [radialEulerRatio_eq_logRatio hRminus hRplus hminus hplus]
    exact hlogRatio
  have hstat : theta * radialEulerDefect 1 r z -
      radialEulerDefect (channelRho (alpha : ℝ)) r z = 0 :=
    (radial_stationary_iff_ratio hminus hplus).2 hratio
  refine ⟨z, hz, ?_, hstat⟩
  dsimp [z]
  simp [canonicalRadialProfile, hr.1]

end CourtadeKumar
