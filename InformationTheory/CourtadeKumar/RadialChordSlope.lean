import InformationTheory.CourtadeKumar.RadialContactShape

/-! Calculus assembly for the centered radial chord. -/

open Set

namespace CourtadeKumar

noncomputable def radialProfileSlope (c : ℝ → ℝ) (r : ℝ) : ℝ :=
  c r / r

/-- The precise V-shape property of `c(r)/r` that produces the chord from
the origin. -/
def RadialSlopeVShape (c : ℝ → ℝ) (rstar : ℝ) : Prop :=
  AntitoneOn (radialProfileSlope c) (Ioc (0 : ℝ) rstar) ∧
    MonotoneOn (radialProfileSlope c) (Icc rstar 1)

theorem hasDerivAt_radialProfileSlope
    {c : ℝ → ℝ} {r cr : ℝ}
    (hr : r ≠ 0) (hc : HasDerivAt c cr r) :
    HasDerivAt (radialProfileSlope c)
      ((r * cr - c r) / r ^ 2) r := by
  unfold radialProfileSlope
  have hquot := hc.div (hasDerivAt_id r) hr
  convert hquot using 1 <;>
    simp only [id_eq] <;>
    field_simp [hr] <;> ring

/-- A V-shaped radial slope is exactly enough to provide the global chord
minorant used by the centered perspective phase. -/
theorem radialChordSupport_of_slopeVShape
    {c : ℝ → ℝ} {rstar : ℝ}
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hc0 : c 0 = 0)
    (hshape : RadialSlopeVShape c rstar) :
    RadialChordSupport c rstar := by
  refine ⟨hrstar.1, hrstar.2.le, ?_⟩
  intro r hr
  rcases hr.1.eq_or_lt with rfl | hrpos
  · simp [hc0]
  · have hslope : radialProfileSlope c rstar ≤ radialProfileSlope c r := by
      rcases le_total r rstar with hle | hge
      · exact hshape.1 ⟨hrpos, hle⟩ ⟨hrstar.1, le_rfl⟩ hle
      · exact hshape.2 ⟨le_rfl, hrstar.2.le⟩ ⟨hge, hr.2⟩ hge
    unfold radialProfileSlope at hslope
    rw [div_le_div_iff₀ hrstar.1 hrpos] at hslope
    calc
      c rstar / rstar * r ≤ c r := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hrstar.1).2 (by
          have := hslope
          nlinarith [mul_pos hrstar.1 hrpos])

/-- Strict derivative signs on the two open sides, together with continuity,
produce the V-shape needed by the chord theorem. -/
theorem radialSlopeVShape_of_derivative_sign
    {c : ℝ → ℝ} {rstar : ℝ}
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcontLeft : ContinuousOn (radialProfileSlope c) (Ioc (0 : ℝ) rstar))
    (hcontRight : ContinuousOn (radialProfileSlope c) (Icc rstar 1))
    (hleft : ∀ r ∈ Ioo (0 : ℝ) rstar,
      deriv (radialProfileSlope c) r < 0)
    (hright : ∀ r ∈ Ioo rstar 1,
      0 < deriv (radialProfileSlope c) r) :
    RadialSlopeVShape c rstar := by
  constructor
  · exact (strictAntiOn_of_deriv_neg (convex_Ioc (0 : ℝ) rstar)
      hcontLeft (by simpa only [interior_Ioc] using hleft)).antitoneOn
  · exact (strictMonoOn_of_deriv_pos (convex_Icc rstar 1)
      hcontRight (by simpa only [interior_Icc] using hright)).monotoneOn

end CourtadeKumar
