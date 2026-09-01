import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Four-corner bounds for the compact-`V` grouped term

This file isolates the elementary algebra behind a grouped compact-`V`
certificate.  The relevant expression

`w * (T - h) + lambda * (1 - w) * (g - T)`

is affine in either `w` or `T` when the other variable is fixed.  It is
therefore bounded below on a rectangle by the minimum of its four corners.
The certificate-facing definitions evaluate those corners exactly in `ℚ`;
the final theorem casts the resulting rational minimum to `ℝ`.

No sign assumption on `lambda` is needed for this separately affine
argument.
-/

set_option autoImplicit false

namespace CourtadeKumar

/-- An affine function on a real interval is bounded below by the smaller of
its two endpoint values.  Splitting on the slope avoids division and does not
require the interval to have positive width. -/
theorem affineEndpointMin_le
    {a b lo hi x : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    min (a * lo + b) (a * hi + b) ≤ a * x + b := by
  by_cases ha : 0 ≤ a
  · have hmul := mul_le_mul_of_nonneg_left hlo ha
    have hadd : a * lo + b ≤ a * x + b := by
      simpa [add_comm] using add_le_add_right hmul b
    exact (min_le_left _ _).trans hadd
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hmul := mul_le_mul_of_nonpos_left hhi ha'
    have hadd : a * hi + b ≤ a * x + b := by
      simpa [add_comm] using add_le_add_right hmul b
    exact (min_le_right _ _).trans hadd

/-- The real grouped term whose variables `w` and `T` are certified by a
rectangle. -/
def lrCompactVGroupedBilinearReal
    (lambda w T g h : ℝ) : ℝ :=
  w * (T - h) + lambda * (1 - w) * (g - T)

theorem lrCompactVGroupedBilinearReal_eq_affine_w
    (lambda w T g h : ℝ) :
    lrCompactVGroupedBilinearReal lambda w T g h =
      ((T - h) - lambda * (g - T)) * w + lambda * (g - T) := by
  simp only [lrCompactVGroupedBilinearReal]
  ring

theorem lrCompactVGroupedBilinearReal_eq_affine_T
    (lambda w T g h : ℝ) :
    lrCompactVGroupedBilinearReal lambda w T g h =
      (w - lambda * (1 - w)) * T +
        (-w * h + lambda * (1 - w) * g) := by
  simp only [lrCompactVGroupedBilinearReal]
  ring

/-- Exact rational evaluation of one grouped-term corner. -/
def lrCompactVGroupedBilinearTerm
    (lambda w T g h : ℚ) : ℚ :=
  w * (T - h) + lambda * (1 - w) * (g - T)

/-- Exact rational minimum of the four corners of a `(w,T)` rectangle.

The corners are grouped first by the `T` endpoint.  This shape is convenient
for the two successive affine endpoint reductions in the soundness proof.
-/
def lrCompactVGroupedBilinearCornerLower
    (lambda wLo wHi TLo THi g h : ℚ) : ℚ :=
  min
    (min
      (lrCompactVGroupedBilinearTerm lambda wLo TLo g h)
      (lrCompactVGroupedBilinearTerm lambda wHi TLo g h))
    (min
      (lrCompactVGroupedBilinearTerm lambda wLo THi g h)
      (lrCompactVGroupedBilinearTerm lambda wHi THi g h))

@[simp] theorem cast_lrCompactVGroupedBilinearTerm
    (lambda w T g h : ℚ) :
    (lrCompactVGroupedBilinearTerm lambda w T g h : ℝ) =
      lrCompactVGroupedBilinearReal
        (lambda : ℝ) (w : ℝ) (T : ℝ) (g : ℝ) (h : ℝ) := by
  simp [lrCompactVGroupedBilinearTerm, lrCompactVGroupedBilinearReal]

/-- A separately affine grouped term is bounded below on a real rectangle by
the minimum of its four real corner values. -/
theorem lrCompactVGroupedBilinear_fourCornerMin_le
    {lambda wLo wHi TLo THi g h w T : ℝ}
    (hwLo : wLo ≤ w) (hwHi : w ≤ wHi)
    (hTLo : TLo ≤ T) (hTHi : T ≤ THi) :
    min
        (min
          (lrCompactVGroupedBilinearReal lambda wLo TLo g h)
          (lrCompactVGroupedBilinearReal lambda wHi TLo g h))
        (min
          (lrCompactVGroupedBilinearReal lambda wLo THi g h)
          (lrCompactVGroupedBilinearReal lambda wHi THi g h)) ≤
      lrCompactVGroupedBilinearReal lambda w T g h := by
  have hwEndpoint (T0 : ℝ) :
      min
          (lrCompactVGroupedBilinearReal lambda wLo T0 g h)
          (lrCompactVGroupedBilinearReal lambda wHi T0 g h) ≤
        lrCompactVGroupedBilinearReal lambda w T0 g h := by
    simpa only [lrCompactVGroupedBilinearReal_eq_affine_w] using
      (affineEndpointMin_le
      (a := (T0 - h) - lambda * (g - T0))
      (b := lambda * (g - T0)) hwLo hwHi)
  have hTEndpoint :
      min
          (lrCompactVGroupedBilinearReal lambda w TLo g h)
          (lrCompactVGroupedBilinearReal lambda w THi g h) ≤
        lrCompactVGroupedBilinearReal lambda w T g h := by
    simpa only [lrCompactVGroupedBilinearReal_eq_affine_T] using
      (affineEndpointMin_le
      (a := w - lambda * (1 - w))
      (b := -w * h + lambda * (1 - w) * g) hTLo hTHi)
  apply (le_min
    ((min_le_left _ _).trans (hwEndpoint TLo))
    ((min_le_right _ _).trans (hwEndpoint THi))).trans
  exact hTEndpoint

/-- Kernel-checkable soundness theorem for the rational four-corner
certificate.  Rational data determine the four corners computationally,
while `w` and `T` may be arbitrary real points in the cast endpoint
rectangle. -/
theorem cast_lrCompactVGroupedBilinearCornerLower_le
    {lambda wLo wHi TLo THi g h : ℚ} {w T : ℝ}
    (hwLo : (wLo : ℝ) ≤ w) (hwHi : w ≤ (wHi : ℝ))
    (hTLo : (TLo : ℝ) ≤ T) (hTHi : T ≤ (THi : ℝ)) :
    (lrCompactVGroupedBilinearCornerLower
        lambda wLo wHi TLo THi g h : ℝ) ≤
      lrCompactVGroupedBilinearReal
        (lambda : ℝ) w T (g : ℝ) (h : ℝ) := by
  change
    ((min
      (min
        (lrCompactVGroupedBilinearTerm lambda wLo TLo g h)
        (lrCompactVGroupedBilinearTerm lambda wHi TLo g h))
      (min
        (lrCompactVGroupedBilinearTerm lambda wLo THi g h)
        (lrCompactVGroupedBilinearTerm lambda wHi THi g h)) : ℚ) : ℝ) ≤ _
  rw [Rat.cast_min, Rat.cast_min, Rat.cast_min]
  simp only [cast_lrCompactVGroupedBilinearTerm]
  exact lrCompactVGroupedBilinear_fourCornerMin_le
    hwLo hwHi hTLo hTHi

end CourtadeKumar
