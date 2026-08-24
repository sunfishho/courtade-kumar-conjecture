import InformationTheory.CourtadeKumar.RadialPerspectiveUnimodal

/-! Construction of attained radial contact profiles from stationary roots. -/

open Set
open scoped NNReal

namespace CourtadeKumar

lemma radialTriangleDifference_zeroRay
    (alpha : ℝ≥0) (theta z : ℝ) :
    radialTriangleDifference alpha theta 0 z =
      (1 - theta) * binaryEntropyBits z := by
  unfold radialTriangleDifference radialTriangleChannelEntropy
    radialTriangleEntropy
  simp
  ring

/-- Stationary roots on all nondegenerate interior rays, already evaluated
by the proposed radial profile. -/
def RadialInteriorStationaryProfile
    (alpha : ℝ≥0) (theta : ℝ) (c : ℝ → ℝ) : Prop :=
  ∀ r ∈ Ioo (0 : ℝ) 1,
    ∃ z ∈ Ioo (0 : ℝ) (1 + r)⁻¹,
      c r = radialTriangleDifference alpha theta r z / z ∧
        theta * radialEulerDefect 1 r z -
          radialEulerDefect (channelRho (alpha : ℝ)) r z = 0

/-- The separate singular-ray contact required at `r = 1`. -/
def RadialOneRayContact
    (alpha : ℝ≥0) (theta : ℝ) (c : ℝ → ℝ) : Prop :=
  ∃ z : ℝ, 0 < z ∧ z ≤ 1 / 2 ∧
    c 1 = radialTriangleDifference alpha theta 1 z / z ∧
      ∀ w : ℝ, 0 < w → w ≤ 1 / 2 →
        c 1 ≤ radialTriangleDifference alpha theta 1 w / w

/-- Interior stationarity now supplies all radial minimization fields. The
zero ray is explicit; only the analytically singular ray `r = 1` is kept as
a separate boundary input. -/
theorem radialContactProfile_of_stationaryRoots
    {alpha : ℝ≥0} {theta : ℝ} {c : ℝ → ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ≤ 1)
    (hc0 : c 0 = 0)
    (hstationary : RadialInteriorStationaryProfile alpha theta c)
    (hone : RadialOneRayContact alpha theta c) :
    RadialContactProfile alpha theta c := by
  intro r hr
  rcases hr.1.eq_or_lt with rfl | hrpos
  · refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩
    · rw [hc0]
      simp [radialTriangleDifference_zeroRay, binaryEntropyBits,
        Real.binEntropy]
    · intro w hw0 hwcap
      rw [hc0, radialTriangleDifference_zeroRay]
      have hw : w ∈ Icc (0 : ℝ) 1 := ⟨hw0.le, by simpa using hwcap⟩
      exact div_nonneg
        (mul_nonneg (sub_nonneg.2 htheta)
          (binaryEntropyBits_nonneg_of_mem_Icc hw)) hw0.le
  · rcases hr.2.eq_or_lt with rfl | hrlt
    · obtain ⟨z, hz0, hzcap, hc, hmin⟩ := hone
      refine ⟨z, hz0, ?_, hc, ?_⟩
      · norm_num at hzcap ⊢
        exact hzcap
      intro w hw0 hwcap
      apply hmin w hw0
      norm_num at hwcap ⊢
      exact hwcap
    · obtain ⟨z, hz, hc, hstat⟩ := hstationary r ⟨hrpos, hrlt⟩
      refine ⟨z, hz.1, by simpa [one_div] using hz.2.le, hc, ?_⟩
      intro w hw0 hwcap
      rw [hc]
      exact radialTriangleDifference_div_min_of_stationary
        halpha ⟨hrpos, hrlt⟩ hz hstat w hw0 (by simpa [one_div] using hwcap)

end CourtadeKumar
