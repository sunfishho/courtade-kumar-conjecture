import InformationTheory.CourtadeKumar.RadialPerspective

/-! Attained radial profiles and their chord supports. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- `c(r)` is the attained minimum of the perspective quotient on every
admissible ray.  This is deliberately stated with an explicit minimizer, so
later code cannot silently use an unattained infimum. -/
def RadialContactProfile
    (alpha : ℝ≥0) (theta : ℝ) (c : ℝ → ℝ) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) 1,
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 / (1 + r) ∧
      c r = radialTriangleDifference alpha theta r z / z ∧
      ∀ w : ℝ, 0 < w → w ≤ 1 / (1 + r) →
        c r ≤ radialTriangleDifference alpha theta r w / w

@[simp] lemma radialTriangleEntropy_zero (r : ℝ) :
    radialTriangleEntropy r 0 = 0 := by
  simp [radialTriangleEntropy, binaryEntropyBits, Real.binEntropy]

@[simp] lemma radialTriangleChannelEntropy_zero
    (alpha : ℝ≥0) (r : ℝ) :
    radialTriangleChannelEntropy alpha r 0 = 0 := by
  simp [radialTriangleChannelEntropy, binaryEntropyBits, Real.binEntropy]

@[simp] lemma radialTriangleDifference_zero
    (alpha : ℝ≥0) (theta r : ℝ) :
    radialTriangleDifference alpha theta r 0 = 0 := by
  simp [radialTriangleDifference]

/-- An attained radial profile automatically supplies the homogeneous
pointwise lower bound required by the perspective argument. -/
theorem radialPerspectiveLowerBound_of_contactProfile
    {alpha : ℝ≥0} {theta : ℝ} {c : ℝ → ℝ}
    (hcontact : RadialContactProfile alpha theta c) :
    RadialPerspectiveLowerBound alpha theta c := by
  intro r z hr hz0 hzcap
  rcases hz0.eq_or_lt with rfl | hz
  · simp
  · obtain ⟨zstar, hzstar, hzstarCap, hc, hmin⟩ := hcontact r hr
    have hquot := hmin z hz hzcap
    calc
      z * c r = c r * z := by ring
      _ ≤ radialTriangleDifference alpha theta r z := (le_div_iff₀ hz).mp hquot

/-- The chord from the origin to `rstar` supports the radial profile on the
whole shape interval. -/
def RadialChordSupport (c : ℝ → ℝ) (rstar : ℝ) : Prop :=
  0 < rstar ∧ rstar ≤ 1 ∧
    ∀ r ∈ Icc (0 : ℝ) 1, c rstar / rstar * r ≤ c r

theorem radialAffineMinorant_of_chord
    {c : ℝ → ℝ} {rstar : ℝ} (hchord : RadialChordSupport c rstar) :
    RadialAffineMinorant c 0 (c rstar / rstar) := by
  intro r hr
  simpa using hchord.2.2 r hr

/-- Combining attained radial minimizers with the supporting chord gives
the centered-endpoint global affine support. -/
theorem triangleAffineSupport_of_radialChord
    {alpha : ℝ≥0} {theta rstar : ℝ} {c : ℝ → ℝ}
    (hcontact : RadialContactProfile alpha theta c)
    (hchord : RadialChordSupport c rstar) :
    TriangleAffineSupport alpha theta 0 (c rstar / rstar) :=
  triangleAffineSupport_of_radialPerspective
    (radialPerspectiveLowerBound_of_contactProfile hcontact)
    (radialAffineMinorant_of_chord hchord)

/-- A tangent (or any affine minorant) together with attained radial
minimizers gives the single-ray global support. -/
theorem triangleAffineSupport_of_radialMinorant
    {alpha : ℝ≥0} {theta a b : ℝ} {c : ℝ → ℝ}
    (hcontact : RadialContactProfile alpha theta c)
    (hminor : RadialAffineMinorant c a b) :
    TriangleAffineSupport alpha theta a b :=
  triangleAffineSupport_of_radialPerspective
    (radialPerspectiveLowerBound_of_contactProfile hcontact) hminor

end CourtadeKumar
