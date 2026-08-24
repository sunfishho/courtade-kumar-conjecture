import InformationTheory.CourtadeKumar.CanonicalRadialChord

/-! Global tangent supports for canonical contacts beyond the centered threshold. -/

open Filter Set
open scoped NNReal Topology

namespace CourtadeKumar

/-- At every canonical contact strictly beyond the centered threshold, the
profile tangent is a global affine minorant on the entire radial interval.
The left part is controlled by the centered chord, the right part by strict
convexity, and the singular endpoint `r = 1` by the fixed one-ray minimizer. -/
theorem canonicalRadialTangentMinorant
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo rstar 1) :
    let c := canonicalRadialProfile alpha theta halpha htheta
    RadialAffineMinorant c
      (c r - r * deriv c r) (deriv c r) := by
  let c := canonicalRadialProfile alpha theta halpha htheta
  let b := deriv c r
  let a := c r - r * b
  have hr01 : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨hrstar.1.trans hr.1, hr.2⟩
  have hconv : StrictConvexOn ℝ (Ico rstar 1) c :=
    strictConvexOn_canonicalRadialProfile_after_threshold
      halpha htheta hrstar hcenter
  have hrmem : r ∈ Ico rstar 1 := ⟨hr.1.le, hr.2⟩
  have hdr0 := hasDerivAt_canonicalRadialProfile halpha htheta hr01
  have hdr : HasDerivAt c b r := by
    exact hdr0.congr_deriv hdr0.deriv.symm
  have hright : ∀ {x : ℝ}, x ∈ Ico rstar 1 → a + b * x ≤ c x := by
    intro x hx
    rcases lt_trichotomy x r with hxr | rfl | hrx
    · have hslope : slope c x r < b :=
        hconv.slope_lt_of_hasDerivAt hx hrmem hxr hdr
      rw [slope_def_field] at hslope
      have hslope' := (div_lt_iff₀ (sub_pos.mpr hxr)).1 hslope
      dsimp [a, b]
      nlinarith
    · dsimp [a, b]
      ring_nf
      exact le_rfl
    · have hslope : b < slope c r x :=
        hconv.lt_slope_of_hasDerivAt hrmem hx hrx hdr
      rw [slope_def_field] at hslope
      have hslope' := (lt_div_iff₀ (sub_pos.mpr hrx)).1 hslope
      dsimp [a, b]
      nlinarith
  have hleft : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) rstar → a + b * x ≤ c x := by
    intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hrstar.2.le⟩
    have hchord := canonicalRadialChordSupport
      halpha htheta hrstar hcenter
    have hchordx : c rstar / rstar * x ≤ c x :=
      hchord.2.2 x hx01
    have hcstar := canonicalRadialProfile_centered_tangent
      halpha htheta hrstar hcenter
    have hk : c rstar / rstar = deriv c rstar := by
      change c rstar = rstar * deriv c rstar at hcstar
      rw [hcstar]
      field_simp [hrstar.1.ne']
    have hrstarmem : rstar ∈ Ico rstar 1 := ⟨le_rfl, hrstar.2⟩
    have hslope : slope c rstar r < b :=
      hconv.slope_lt_of_hasDerivAt hrstarmem hrmem hr.1 hdr
    have hderivstar : deriv c rstar < b := by
      have hdrstar0 := hasDerivAt_canonicalRadialProfile
        halpha htheta hrstar
      have hdrstar : HasDerivAt c (deriv c rstar) rstar := by
        exact hdrstar0.congr_deriv hdrstar0.deriv.symm
      exact (hconv.lt_slope_of_hasDerivAt
        hrstarmem hrmem hr.1 hdrstar).trans hslope
    rw [slope_def_field] at hslope
    have hslope' := (div_lt_iff₀ (sub_pos.mpr hr.1)).1 hslope
    have hmul : (b - c rstar / rstar) * (x - rstar) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · rw [hk]
        exact (sub_pos.mpr hderivstar).le
      · linarith [hx.2]
    have hkstar : c rstar / rstar * rstar = c rstar := by
      field_simp [hrstar.1.ne']
    have hatstar : a + b * rstar ≤ c rstar / rstar * rstar := by
      dsimp [a, b]
      nlinarith [hslope', hkstar]
    have hline : a + b * x ≤ c rstar / rstar * x := by
      nlinarith [hatstar, hmul]
    exact hline.trans hchordx
  have hone : a + b ≤ c 1 := by
    obtain ⟨z1, hz1, hz1cap, hc1, _⟩ :=
      canonicalRadialProfile_oneRayContact halpha htheta
    have hcontact := canonicalRadialProfile_contactProfile halpha htheta
    let g : ℝ → ℝ := fun x ↦
      radialTriangleDifference alpha theta x z1 / z1
    let L : ℝ → ℝ := fun x ↦ a + b * x
    have hDcont : Continuous (fun x : ℝ ↦
        radialTriangleDifference alpha theta x z1) := by
      unfold radialTriangleDifference radialTriangleChannelEntropy
        radialTriangleEntropy binaryEntropyBits
      fun_prop
    have hgcont : ContinuousAt g 1 := by
      dsimp [g]
      exact hDcont.div_const z1 |>.continuousAt
    have hLcont : ContinuousAt L 1 := by
      dsimp [L]
      fun_prop
    have hg1 : g 1 = c 1 := by
      dsimp [g]
      exact hc1.symm
    have hnear : ∀ᶠ x in nhdsWithin (1 : ℝ) (Iio 1), x ∈ Ico rstar 1 := by
      have hgt : ∀ᶠ x in nhdsWithin (1 : ℝ) (Iio 1), r < x :=
        (eventually_gt_nhds hr.2).filter_mono nhdsWithin_le_nhds
      have hlt : ∀ᶠ x in nhdsWithin (1 : ℝ) (Iio 1), x < 1 :=
        self_mem_nhdsWithin
      filter_upwards [hgt, hlt] with x hrx hx1
      exact ⟨hr.1.le.trans hrx.le, hx1⟩
    have hbound : ∀ᶠ x in nhdsWithin (1 : ℝ) (Iio 1), L x ≤ g x := by
      filter_upwards [hnear] with x hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 :=
        ⟨hrstar.1.le.trans hx.1, hx.2.le⟩
      have hden : 0 < 1 + x := by linarith [hrstar.1, hx.1]
      have hzcapx : z1 ≤ 1 / (1 + x) := by
        calc
          z1 ≤ 1 / 2 := hz1cap
          _ ≤ 1 / (1 + x) := by
            rw [le_div_iff₀ hden]
            nlinarith [hx.2]
      have hcand : c x ≤ g x := by
        obtain ⟨_, _, _, _, hmin⟩ := hcontact x hx01
        dsimp [g]
        exact hmin z1 hz1 hzcapx
      exact (hright hx).trans hcand
    have htL : Tendsto L (nhdsWithin (1 : ℝ) (Iio 1)) (nhds (a + b)) := by
      simpa [L] using hLcont.tendsto.mono_left nhdsWithin_le_nhds
    have htg : Tendsto g (nhdsWithin (1 : ℝ) (Iio 1)) (nhds (c 1)) := by
      rw [← hg1]
      exact hgcont.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto htL htg hbound
  dsimp [RadialAffineMinorant]
  intro x hx
  rcases hx.2.eq_or_lt with rfl | hx1
  · simpa using hone
  · by_cases hxrstar : x ≤ rstar
    · exact hleft ⟨hx.1, hxrstar⟩
    · exact hright ⟨le_of_not_ge hxrstar, hx1⟩

/-- The canonical single-ray tangent therefore gives a global affine
support for the ordered-triangle Lagrangian. -/
theorem canonicalSingleRayTriangleAffineSupport
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hr : r ∈ Ioo rstar 1) :
    let c := canonicalRadialProfile alpha theta halpha htheta
    TriangleAffineSupport alpha theta
      (c r - r * deriv c r) (deriv c r) := by
  exact triangleAffineSupport_of_radialMinorant
    (canonicalRadialProfile_contactProfile halpha htheta)
    (canonicalRadialTangentMinorant halpha htheta hrstar hcenter hr)

end CourtadeKumar
