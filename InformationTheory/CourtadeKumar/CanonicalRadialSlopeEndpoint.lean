import InformationTheory.CourtadeKumar.CanonicalRadialSlopeLeft
import InformationTheory.CourtadeKumar.RadialOneRay

/-! Closure of right radial-slope monotonicity at the singular ray. -/

open Filter Set
open scoped NNReal Topology

namespace CourtadeKumar

theorem canonicalRadialProfileSlope_le_one
    {alpha : ℝ≥0} {theta rstar x : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta)
    (hx : x ∈ Ico rstar 1) :
    radialProfileSlope
        (canonicalRadialProfile alpha theta halpha htheta) x ≤
      radialProfileSlope
        (canonicalRadialProfile alpha theta halpha htheta) 1 := by
  let c := canonicalRadialProfile alpha theta halpha htheta
  obtain ⟨z1, hz1, hz1cap, hc1, hmin1⟩ :=
    canonicalRadialProfile_oneRayContact halpha htheta
  let g : ℝ → ℝ := fun r ↦
    (radialTriangleDifference alpha theta r z1 / z1) / r
  have hDcont : Continuous (fun r : ℝ ↦
      radialTriangleDifference alpha theta r z1) := by
    unfold radialTriangleDifference radialTriangleChannelEntropy
      radialTriangleEntropy binaryEntropyBits
    fun_prop
  have hgcont : ContinuousAt g 1 := by
    dsimp [g]
    exact (hDcont.div_const z1).continuousAt.div continuousAt_id one_ne_zero
  have hg1 : g 1 = radialProfileSlope c 1 := by
    dsimp [g, c, radialProfileSlope]
    rw [hc1]
  have hgt : ∀ᶠ r in nhdsWithin (1 : ℝ) (Iio 1), x < r := by
    exact (eventually_gt_nhds hx.2).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r in nhdsWithin (1 : ℝ) (Iio 1), r < 1 :=
    self_mem_nhdsWithin
  have hnear : ∀ᶠ r in nhdsWithin (1 : ℝ) (Iio 1), r ∈ Ioo rstar 1 := by
    filter_upwards [hgt, hlt] with r hxr hr1
    exact ⟨hx.1.trans_lt hxr, hr1⟩
  have hcontact := canonicalRadialProfile_contactProfile halpha htheta
  have hmono := strictMonoOn_radialProfileSlope_after_threshold
    halpha htheta hrstar hcenter
  have hbound : ∀ᶠ r in nhdsWithin (1 : ℝ) (Iio 1),
      radialProfileSlope c x ≤ g r := by
    filter_upwards [hgt, hnear] with r hxr hr
    have hxmem : x ∈ Ico rstar 1 := hx
    have hrmem : r ∈ Ico rstar 1 := ⟨hr.1.le, hr.2⟩
    have hslope : radialProfileSlope c x ≤ radialProfileSlope c r :=
      (hmono hxmem hrmem hxr).le
    have hrIcc : r ∈ Icc (0 : ℝ) 1 :=
      ⟨hrstar.1.le.trans hr.1.le, hr.2.le⟩
    obtain ⟨_, _, _, _, hmin⟩ := hcontact r hrIcc
    have h1r : 0 < 1 + r := by linarith [hrstar.1, hr.1]
    have hzcap : z1 ≤ 1 / (1 + r) := by
      calc
        z1 ≤ 1 / 2 := hz1cap
        _ ≤ 1 / (1 + r) := by
          rw [le_div_iff₀ h1r]
          nlinarith [hr.2]
    have hcand : c r ≤ radialTriangleDifference alpha theta r z1 / z1 :=
      hmin z1 hz1 hzcap
    have hslopeCand : radialProfileSlope c r ≤ g r := by
      unfold radialProfileSlope
      dsimp [g]
      exact (div_le_div_iff_of_pos_right (hrstar.1.trans hr.1)).2 hcand
    exact hslope.trans hslopeCand
  have htendsto : Tendsto g (nhdsWithin (1 : ℝ) (Iio 1))
      (nhds (radialProfileSlope c 1)) := by
    rw [← hg1]
    exact hgcont.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htendsto hbound

theorem monotoneOn_radialProfileSlope_after_threshold_closed
    {alpha : ℝ≥0} {theta rstar : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ))
      rstar (1 / 2) = theta) :
    MonotoneOn (radialProfileSlope
      (canonicalRadialProfile alpha theta halpha htheta))
      (Icc rstar 1) := by
  intro x hx y hy hxy
  rcases hy.2.eq_or_lt with rfl | hy1
  · rcases hx.2.eq_or_lt with rfl | hx1
    · exact le_rfl
    · exact canonicalRadialProfileSlope_le_one
        halpha htheta hrstar hcenter ⟨hx.1, hx1⟩
  · rcases hxy.eq_or_lt with rfl | hxylt
    · exact le_rfl
    · exact (strictMonoOn_radialProfileSlope_after_threshold
        halpha htheta hrstar hcenter
        ⟨hx.1, hxylt.trans hy1⟩ ⟨hy.1, hy1⟩ hxylt).le

end CourtadeKumar
