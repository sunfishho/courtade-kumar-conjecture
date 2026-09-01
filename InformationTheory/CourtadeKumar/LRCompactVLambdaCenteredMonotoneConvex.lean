import InformationTheory.CourtadeKumar.LRCompactVLambdaCenteredPolynomialDerivatives
import Mathlib.Analysis.Convex.Deriv

/-!
# Monotone-convex terminal for the centered compact-V polynomial

On the difficult high-parameter compact-`V` region, interval diagnostics show
that the centered polynomial is decreasing in `v` and convex in `x`.  A leaf
can therefore move directly to `vHi` and use the tangent line at one `x`
center.  Compared with a two-variable Taylor leaf, this pays no Hessian
remainder at all: the checker only needs the signs of `P_v` and `P_xx`, the
center value, and the center `x`-gradient.

The result is especially useful for reducing generated terminal count.  It
does not assume that the diagnostic signs hold: each eventual leaf must
kernel-check them on its complete rectangle.
-/

set_option autoImplicit false

open Set

namespace CourtadeKumar

/-- A differentiable convex real function lies above its tangent line at an
interior or endpoint point of the convexity interval. -/
private theorem tangent_lower_of_convexOn
    {f : ℝ → ℝ} {xLo xCenter x xHi slope : ℝ}
    (hconvex : ConvexOn ℝ (Icc xLo xHi) f)
    (hcenter : xCenter ∈ Icc xLo xHi)
    (hx : x ∈ Icc xLo xHi)
    (hderiv : HasDerivAt f slope xCenter) :
    f xCenter + slope * (x - xCenter) ≤ f x := by
  rcases lt_trichotomy x xCenter with hleft | heq | hright
  · have hslope := hconvex.slope_le_of_hasDerivAt
      hx hcenter hleft hderiv
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ (sub_pos.mpr hleft)).mp hslope
    calc
      f xCenter + slope * (x - xCenter) =
          f xCenter - slope * (xCenter - x) := by ring
      _ ≤ f x := by linarith
  · subst x
    simp
  · have hslope := hconvex.le_slope_of_hasDerivAt
      hcenter hx hright hderiv
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hright)).mp hslope
    linarith

/-- When both first partials are nonpositive, the upper-right corner is a
lower bound for the whole rectangle.  This is the cheapest terminal used by
the reduced adjacent-domain topology. -/
theorem lrCompactVLambdaCenteredPolynomialFinite_monotone_corner_lower
    (N : ℕ) (lambda R v vHi x xHi lower : ℝ)
    (hv : v ≤ vHi) (hx : x ≤ xHi)
    (hvalue :
      lower ≤
        lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi xHi)
    (hPv : ∀ qv ∈ Icc v vHi,
      lrCompactVLambdaCenteredPolynomialV N lambda R qv x ≤ 0)
    (hPx : ∀ qx ∈ Icc x xHi,
      lrCompactVLambdaCenteredPolynomialX N lambda R vHi qx ≤ 0) :
    lower ≤
      lrCompactVLambdaCenteredPolynomialFinite N lambda R v x := by
  let fv : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialFinite N lambda R q x
  let fvv : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialV N lambda R q x
  have hvAnti : AntitoneOn fv (Icc v vHi) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fvv) (convex_Icc v vHi) ?_ ?_ ?_
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_v
        N lambda R q x).continuousAt.continuousWithinAt
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_v
        N lambda R q x).hasDerivWithinAt
    · intro q hq
      exact hPv q (interior_subset hq)
  have hvStep :
      lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi x ≤
        lrCompactVLambdaCenteredPolynomialFinite N lambda R v x := by
    exact hvAnti ⟨le_rfl, hv⟩ ⟨hv, le_rfl⟩ hv
  let fx : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi q
  let fxx : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialX N lambda R vHi q
  have hxAnti : AntitoneOn fx (Icc x xHi) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fxx) (convex_Icc x xHi) ?_ ?_ ?_
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_x
        N lambda R vHi q).continuousAt.continuousWithinAt
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_x
        N lambda R vHi q).hasDerivWithinAt
    · intro q hq
      exact hPx q (interior_subset hq)
  have hxStep :
      lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi xHi ≤
        lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi x := by
    exact hxAnti ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  exact hvalue.trans (hxStep.trans hvStep)

/-- If `P_v ≤ 0` on the vertical segment and `P_xx ≥ 0` on the
horizontal box, then a center tangent at the top `v` endpoint is a lower
bound throughout the rectangle.  The final absolute-gradient estimate is
stated in evaluator-facing form. -/
theorem lrCompactVLambdaCenteredPolynomialFinite_monotone_convex_lower
    (N : ℕ) (lambda R v vHi xLo xCenter x xHi : ℝ)
    (lower gradientRadius xRadius : ℝ)
    (hv : v ≤ vHi)
    (hcenter : xCenter ∈ Icc xLo xHi)
    (hx : x ∈ Icc xLo xHi)
    (hgradientRadius : 0 ≤ gradientRadius)
    (hdelta : |x - xCenter| ≤ xRadius)
    (hvalue :
      lower ≤
        lrCompactVLambdaCenteredPolynomialFinite
          N lambda R vHi xCenter)
    (hgradient :
      |lrCompactVLambdaCenteredPolynomialX
          N lambda R vHi xCenter| ≤ gradientRadius)
    (hPv : ∀ qv ∈ Icc v vHi,
      lrCompactVLambdaCenteredPolynomialV N lambda R qv x ≤ 0)
    (hPxx : ∀ qx ∈ Icc xLo xHi,
      0 ≤ lrCompactVLambdaCenteredPolynomialXX
        N lambda R vHi qx) :
    lower - gradientRadius * xRadius ≤
      lrCompactVLambdaCenteredPolynomialFinite N lambda R v x := by
  let fv : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialFinite N lambda R q x
  let fvx : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialV N lambda R q x
  have hvAnti : AntitoneOn fv (Icc v vHi) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fvx) (convex_Icc v vHi) ?_ ?_ ?_
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_v
        N lambda R q x).continuousAt.continuousWithinAt
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_v
        N lambda R q x).hasDerivWithinAt
    · intro q hq
      exact hPv q (interior_subset hq)
  have hvStep :
      lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi x ≤
        lrCompactVLambdaCenteredPolynomialFinite N lambda R v x := by
    exact hvAnti ⟨le_rfl, hv⟩ ⟨hv, le_rfl⟩ hv
  let fx : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi q
  let fxx : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialX N lambda R vHi q
  let fxxx : ℝ → ℝ := fun q ↦
    lrCompactVLambdaCenteredPolynomialXX N lambda R vHi q
  have hxConvex : ConvexOn ℝ (Icc xLo xHi) fx := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fxx) (f'' := fxxx) (convex_Icc xLo xHi) ?_ ?_ ?_ ?_
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_x
        N lambda R vHi q).continuousAt.continuousWithinAt
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_x
        N lambda R vHi q).hasDerivWithinAt
    · intro q hq
      exact (hasDerivAt_lrCompactVLambdaCenteredPolynomialX_x
        N lambda R vHi q).hasDerivWithinAt
    · intro q hq
      exact hPxx q (interior_subset hq)
  have htangent :
      lrCompactVLambdaCenteredPolynomialFinite
          N lambda R vHi xCenter +
          lrCompactVLambdaCenteredPolynomialX
            N lambda R vHi xCenter * (x - xCenter) ≤
        lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi x := by
    exact tangent_lower_of_convexOn hxConvex hcenter hx
      (hasDerivAt_lrCompactVLambdaCenteredPolynomialFinite_x
        N lambda R vHi xCenter)
  have hproductAbs :
      |lrCompactVLambdaCenteredPolynomialX
          N lambda R vHi xCenter * (x - xCenter)| ≤
        gradientRadius * xRadius := by
    rw [abs_mul]
    exact mul_le_mul hgradient hdelta (abs_nonneg _) hgradientRadius
  have hproductLower :
      -(gradientRadius * xRadius) ≤
        lrCompactVLambdaCenteredPolynomialX
          N lambda R vHi xCenter * (x - xCenter) :=
    neg_le_of_abs_le hproductAbs
  calc
    lower - gradientRadius * xRadius ≤
        lrCompactVLambdaCenteredPolynomialFinite
          N lambda R vHi xCenter - gradientRadius * xRadius :=
      sub_le_sub_right hvalue _
    _ ≤ lrCompactVLambdaCenteredPolynomialFinite
          N lambda R vHi xCenter +
        lrCompactVLambdaCenteredPolynomialX
          N lambda R vHi xCenter * (x - xCenter) := by
      linarith
    _ ≤ lrCompactVLambdaCenteredPolynomialFinite N lambda R vHi x :=
      htangent
    _ ≤ lrCompactVLambdaCenteredPolynomialFinite N lambda R v x :=
      hvStep

end CourtadeKumar
