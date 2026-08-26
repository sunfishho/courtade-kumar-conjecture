import InformationTheory.CourtadeKumar.LRLowShapeVL7Certificate

/-! Reusable polynomial bridge for the five finite low-shape `V` heads. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def lrLowVHeadMinorant (v x : ℝ) (n : ℕ) : ℝ :=
  lrLowVComparisonMinorant v x n +
    (n : ℝ) * lrLowALower v x * lrLowPnLower v x n

noncomputable def lrLowVDeltaScaledPolynomial (v z : ℝ) (n : ℕ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  let q := v ^ 2 * x
  let dx := 20 - 17 * z
  let dxi := 20 - 17 * v ^ 2 * z
  (1 - v * x) / 2 *
    (∑ k ∈ Finset.range (n - 1),
      ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
        q ^ (k + 1) * lrLowCStarLower (n - (k + 1))) *
    (1 + v) ^ 8 * (2 + v) ^ 9 * dx * dxi

noncomputable def lrLowVComparisonScaledPolynomial
    (v z : ℝ) (n : ℕ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  lrLowVGPolynomial v z * lrLowEHead (v ^ 2 * x) n -
    (n : ℝ) * lrLowVL7ConstantScaledPolynomial v z * lrLowCStarUpper n +
    lrLowVDeltaScaledPolynomial v z n

noncomputable def lrLowVHeadPolynomial (v z : ℝ) (n : ℕ) : ℝ :=
  let x := (17 / 20 : ℝ) * z
  lrLowVComparisonScaledPolynomial v z n +
    (n : ℝ) *
      (lrLowWALowerRadialNumerator v x *
        (20 - 17 * z) * (20 - 17 * v ^ 2 * z)) *
      lrLowPnLower v x n

lemma lrLowVDelta_mul_base_eq_polynomial
    {v z : ℝ} (h1 : 1 + v ≠ 0) (n : ℕ) :
    lrLowDelta v ((17 / 20 : ℝ) * z) / 2 *
        (∑ k ∈ Finset.range (n - 1),
          ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
            (v ^ 2 * ((17 / 20 : ℝ) * z)) ^ (k + 1) *
              lrLowCStarLower (n - (k + 1))) *
        lrLowVL7CertificateBase v z =
      lrLowVDeltaScaledPolynomial v z n := by
  unfold lrLowDelta lrLowVL7CertificateBase lrLowVDeltaScaledPolynomial
  dsimp only
  field_simp [h1]

lemma lrLowVComparisonMinorant_mul_base_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (n : ℕ) :
    lrLowVComparisonMinorant v ((17 / 20 : ℝ) * z) n *
        lrLowVL7CertificateBase v z =
      lrLowVComparisonScaledPolynomial v z n := by
  have hg := lrLowVG_scaled_eq_polynomial hv hz
  change lrLowGShapeLower v ((17 / 20 : ℝ) * z) *
      lrLowVL7CertificateBase v z = lrLowVGPolynomial v z at hg
  have hc := lrLowVL7Constant_mul_base_eq_polynomial hv hz
  have hd := lrLowVDelta_mul_base_eq_polynomial
    (v := v) (z := z) (by linarith [hv.1]) n
  unfold lrLowVComparisonMinorant lrLowVComparisonScaledPolynomial
  dsimp only
  calc
    (lrLowGShapeLower v (17 / 20 * z) *
          lrLowEHead (v ^ 2 * (17 / 20 * z)) n -
        (n : ℝ) * lrLowVConstantUpper v (17 / 20 * z) * lrLowCStarUpper n +
        lrLowDelta v (17 / 20 * z) / 2 *
          ∑ k ∈ Finset.range (n - 1),
            ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
              (v ^ 2 * (17 / 20 * z)) ^ (k + 1) *
                lrLowCStarLower (n - (k + 1))) * lrLowVL7CertificateBase v z =
      (lrLowGShapeLower v (17 / 20 * z) * lrLowVL7CertificateBase v z) *
          lrLowEHead (v ^ 2 * (17 / 20 * z)) n -
        (n : ℝ) * (lrLowVConstantUpper v (17 / 20 * z) *
          lrLowVL7CertificateBase v z) * lrLowCStarUpper n +
        (lrLowDelta v (17 / 20 * z) / 2 *
          (∑ k ∈ Finset.range (n - 1),
            ((n - (k + 1) : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) *
              (v ^ 2 * (17 / 20 * z)) ^ (k + 1) *
                lrLowCStarLower (n - (k + 1))) *
          lrLowVL7CertificateBase v z) := by ring
    _ = _ := by rw [hg, hc, hd]

theorem lrLowVHeadMinorant_mul_base_eq_polynomial
    {v z : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (n : ℕ) :
    lrLowVHeadMinorant v ((17 / 20 : ℝ) * z) n *
        lrLowVL7CertificateBase v z = lrLowVHeadPolynomial v z n := by
  have hcomparison := lrLowVComparisonMinorant_mul_base_eq_polynomial hv hz n
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  have ha := lrLowALower_mul_radial
    (v := v) (x := (17 / 20 : ℝ) * z) h2
  unfold lrLowVHeadMinorant lrLowVHeadPolynomial
  dsimp only
  rw [add_mul, hcomparison]
  unfold lrLowWRadialBase at ha
  unfold lrLowVL7CertificateBase
  linear_combination (n : ℝ) * lrLowPnLower v (17 / 20 * z) n *
    (20 - 17 * z) * (20 - 17 * v ^ 2 * z) * ha

end CourtadeKumar
