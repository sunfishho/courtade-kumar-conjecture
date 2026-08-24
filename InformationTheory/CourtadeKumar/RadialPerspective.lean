import InformationTheory.CourtadeKumar.OrderedTriangleBoundary

/-! Radial perspective coordinates for affine support certificates. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- Entropy along the ray `(m,u) = (z,r*z)`. -/
noncomputable def radialTriangleEntropy (r z : ℝ) : ℝ :=
  (binaryEntropyBits ((1 - r) * z) +
      binaryEntropyBits ((1 + r) * z)) / 2

/-- Channel entropy along the same ray. -/
noncomputable def radialTriangleChannelEntropy
    (alpha : ℝ≥0) (r z : ℝ) : ℝ :=
  (binaryEntropyBits ((1 - channelRho (alpha : ℝ) * r) * z) +
      binaryEntropyBits ((1 + channelRho (alpha : ℝ) * r) * z)) / 2

noncomputable def radialTriangleDifference
    (alpha : ℝ≥0) (theta r z : ℝ) : ℝ :=
  radialTriangleChannelEntropy alpha r z - theta * radialTriangleEntropy r z

/-- A candidate radial profile is a homogeneous lower bound for the
pointwise Lagrangian on every admissible ray. -/
def RadialPerspectiveLowerBound
    (alpha : ℝ≥0) (theta : ℝ) (c : ℝ → ℝ) : Prop :=
  ∀ (r z : ℝ), r ∈ Icc (0 : ℝ) 1 → 0 ≤ z → z ≤ 1 / (1 + r) →
    z * c r ≤ radialTriangleDifference alpha theta r z

/-- An affine function supporting the radial profile from below. -/
def RadialAffineMinorant (c : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) 1, a + b * r ≤ c r

lemma radialTriangleEntropy_eq_ordered (r z : ℝ) :
    radialTriangleEntropy r z = orderedTriangleEntropy z (r * z) := by
  unfold radialTriangleEntropy orderedTriangleEntropy
  congr 2 <;> ring

lemma radialTriangleChannelEntropy_eq_ordered
    (alpha : ℝ≥0) (r z : ℝ) :
    radialTriangleChannelEntropy alpha r z =
      orderedTriangleChannelEntropy alpha z (r * z) := by
  unfold radialTriangleChannelEntropy orderedTriangleChannelEntropy
  congr 2 <;> ring

lemma radialTriangleDifference_eq_ordered
    (alpha : ℝ≥0) (theta r z : ℝ) :
    radialTriangleDifference alpha theta r z =
      orderedTriangleChannelEntropy alpha z (r * z) -
        theta * orderedTriangleEntropy z (r * z) := by
  rw [radialTriangleDifference, radialTriangleEntropy_eq_ordered,
    radialTriangleChannelEntropy_eq_ordered]

/-- The exact perspective implication: a homogeneous radial lower bound and
an affine minorant of its profile produce a global affine support on the
ordered triangle. -/
theorem triangleAffineSupport_of_radialPerspective
    {alpha : ℝ≥0} {theta a b : ℝ} {c : ℝ → ℝ}
    (hradial : RadialPerspectiveLowerBound alpha theta c)
    (hminor : RadialAffineMinorant c a b) :
    TriangleAffineSupport alpha theta a b := by
  intro m u hu0 hum hu1m
  by_cases hm : m = 0
  · have hu : u = 0 := by linarith
    subst m
    subst u
    have hzero := hradial 0 0 (by simp) (by norm_num) (by norm_num)
    rw [radialTriangleDifference_eq_ordered] at hzero
    simpa using hzero
  · have hm0 : 0 < m := lt_of_le_of_ne (hu0.trans hum) (Ne.symm hm)
    let r : ℝ := u / m
    have hr : r ∈ Icc (0 : ℝ) 1 := by
      dsimp [r]
      constructor
      · exact div_nonneg hu0 hm0.le
      · exact (div_le_one hm0).2 hum
    have hmcap : m ≤ 1 / (1 + r) := by
      have hden : 0 < 1 + r := by linarith [hr.1]
      rw [le_div_iff₀ hden]
      dsimp [r]
      field_simp [hm]
      linarith
    have hpersp := hradial r m hr hm0.le hmcap
    have hminorAt := hminor r hr
    have hscaled := mul_le_mul_of_nonneg_left hminorAt hm0.le
    have hru : r * m = u := by
      dsimp [r]
      field_simp
    rw [radialTriangleDifference_eq_ordered, hru] at hpersp
    calc
      a * m + b * u = m * (a + b * r) := by
        dsimp [r]
        field_simp [hm]
      _ ≤ m * c r := hscaled
      _ ≤ orderedTriangleChannelEntropy alpha m u -
          theta * orderedTriangleEntropy m u := hpersp

end CourtadeKumar
