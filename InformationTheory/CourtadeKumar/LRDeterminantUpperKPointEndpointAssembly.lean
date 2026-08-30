import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedScalarArguments
import InformationTheory.CourtadeKumar.LRDeterminantUpperKPointCachedCornerValues

/-!
# Endpoint assembly from shared upper-`K` point certificates

The generated upper-`K` replay uses the same exact rational `Q/Q'` point in
many scalar endpoint calls.  This module turns imported point values and
their semantic facts into the eight rounded `A/C` scalar enclosures expected
by the point-cached corner evaluator.  No point certificate is rebuilt here.

The assembly is parameterized by `LRUpperKCachedScalarArguments.Arguments`.
That existing record lets a generated leaf authenticate all box geometry
once, rather than normalize `y0AD` and `eAD` separately for every point fact.

Both scalar primitives are exactly zero when `y = 0`.  The explicit `.zero`
constructors below consequently contain no dummy point reference and demand
no fact about the singular value `Q' 0`.
-/

namespace CourtadeKumar
namespace LRUpperKPointEndpointAssembly

open LRUpperKReplayCertificate
open LRUpperKMidpointCoarsening

abbrev PointValues := LRUpperKPointCache.Values
abbrev PointSound := LRUpperKPointCache.Sound
abbrev Arguments := LRUpperKCachedScalarArguments.Arguments
abbrev ScalarValues := LRUpperKPointCachedCornerValues.ScalarValues
abbrev EndpointSound := LRUpperKPointCachedCornerValues.EndpointSound

/-- Compatibility name for the lightweight generated-cache export.  Its
definition lives in `LRDeterminantUpperKPointSoundCore`, so generated point
proofs do not import this endpoint-assembly stack. -/
abbrev CertifiedPoint (terms : ℕ) (z : ℚ) :=
  LRUpperKPointCache.CertifiedPoint terms z

/-- Value data for one `A(s,y)` endpoint.  The zero constructor avoids all
point references; the positive/general constructor stores only the two
enclosures actually used by `aEnclosure`. -/
inductive APointValues where
  | zero
  | ofPoints (atB atS : PointValues)

/-- Reconstruct `A`, then restore the replay's dyadic bit width. -/
def APointValues.enclosure (bits : ℕ) (points : APointValues)
    (s y : ℚ) : RationalEnclosure :=
  match points with
  | .zero => RationalEnclosure.point 0
  | .ofPoints atB atS =>
      LRUpperKDyadicOuterRounding.outerEnclosure bits
        (LRUpperKPointCache.aEnclosure s y atB atS)

/-- Point facts required by an `A` endpoint.  The `.zero` branch is certified
solely by the exact rational argument equality. -/
def APointValues.Sound (points : APointValues) (terms : ℕ)
    (s y : ℚ) : Prop :=
  match points with
  | .zero => y = 0
  | .ofPoints atB atS =>
      PointSound terms (LRUpperKPointCache.bPoint s y) atB ∧
        PointSound terms s atS

theorem APointValues.enclosure_sound (bits terms : ℕ) {s y : ℚ}
    {points : APointValues} (hpoints : points.Sound terms s y) :
    (points.enclosure bits s y).Contains
      (aPrimitive (s : ℝ) (y : ℝ)) := by
  cases points with
  | zero =>
      have hy0 : y = 0 := by
        simpa only [APointValues.Sound] using hpoints
      subst y
      simpa [APointValues.enclosure, aPrimitive, lrCertificateQ_zero] using
        RationalEnclosure.contains_point (0 : ℚ)
  | ofPoints atB atS =>
      have hraw := LRUpperKPointCache.aEnclosure_sound terms
        hpoints.1 hpoints.2
      exact contains_of_covers
        (LRUpperKDyadicOuterRounding.outerEnclosure_covers bits
          (LRUpperKPointCache.aEnclosure s y atB atS)) hraw

/-- Value data for one `C(s,y)` endpoint. -/
inductive CPointValues where
  | zero
  | ofPoints (atB atY atS : PointValues)

/-- Reconstruct `C`, then restore the replay's dyadic bit width. -/
def CPointValues.enclosure (bits : ℕ) (points : CPointValues)
    (s y : ℚ) : RationalEnclosure :=
  match points with
  | .zero => RationalEnclosure.point 0
  | .ofPoints atB atY atS =>
      LRUpperKDyadicOuterRounding.outerEnclosure bits
        (LRUpperKPointCache.cEnclosure s y atB atY atS)

/-- Point facts required by a `C` endpoint. -/
def CPointValues.Sound (points : CPointValues) (terms : ℕ)
    (s y : ℚ) : Prop :=
  match points with
  | .zero => y = 0
  | .ofPoints atB atY atS =>
      PointSound terms (LRUpperKPointCache.bPoint s y) atB ∧
        PointSound terms y atY ∧ PointSound terms s atS

theorem CPointValues.enclosure_sound (bits terms : ℕ) {s y : ℚ}
    {points : CPointValues} (hpoints : points.Sound terms s y) :
    (points.enclosure bits s y).Contains
      (cPrimitive (s : ℝ) (y : ℝ)) := by
  cases points with
  | zero =>
      have hy0 : y = 0 := by
        simpa only [CPointValues.Sound] using hpoints
      subst y
      simpa [CPointValues.enclosure, cPrimitive] using
        RationalEnclosure.contains_point (0 : ℚ)
  | ofPoints atB atY atS =>
      have hraw := LRUpperKPointCache.cEnclosure_sound terms
        hpoints.1 hpoints.2.1 hpoints.2.2
      exact contains_of_covers
        (LRUpperKDyadicOuterRounding.outerEnclosure_covers bits
          (LRUpperKPointCache.cEnclosure s y atB atY atS)) hraw

/-- Point-value inputs for the eight monotone endpoint calls.  Repeated
points (especially in a center box) are represented by repeated references
to the same imported cache constant, not by recomputed certificates. -/
structure EndpointPointValues where
  aY0Lower : APointValues
  aY0Upper : APointValues
  cY0Lower : CPointValues
  cY0Upper : CPointValues
  aELower : APointValues
  aEUpper : APointValues
  cELower : CPointValues
  cEUpper : CPointValues

/-- Assemble exactly the `ScalarValues` consumed by the cached evaluator. -/
def EndpointPointValues.scalarValues (bits : ℕ)
    (points : EndpointPointValues) (arguments : Arguments) : ScalarValues :=
  { aY0Lower := points.aY0Lower.enclosure bits
      arguments.aY0LowerS arguments.aY0LowerY
    aY0Upper := points.aY0Upper.enclosure bits
      arguments.aY0UpperS arguments.aY0UpperY
    cY0Lower := points.cY0Lower.enclosure bits
      arguments.cY0LowerS arguments.cY0LowerY
    cY0Upper := points.cY0Upper.enclosure bits
      arguments.cY0UpperS arguments.cY0UpperY
    aELower := points.aELower.enclosure bits
      arguments.aELowerS arguments.aELowerY
    aEUpper := points.aEUpper.enclosure bits
      arguments.aEUpperS arguments.aEUpperY
    cELower := points.cELower.enclosure bits
      arguments.cELowerS arguments.cELowerY
    cEUpper := points.cEUpper.enclosure bits
      arguments.cEUpperS arguments.cEUpperY }

/-- The point facts for all eight endpoint calls.  This is deliberately a
separate proposition, so evaluation of `scalarValues` never traverses proof
fields. -/
structure EndpointPointValues.Sound (points : EndpointPointValues)
    (terms : ℕ) (arguments : Arguments) : Prop where
  aY0Lower : points.aY0Lower.Sound terms
    arguments.aY0LowerS arguments.aY0LowerY
  aY0Upper : points.aY0Upper.Sound terms
    arguments.aY0UpperS arguments.aY0UpperY
  cY0Lower : points.cY0Lower.Sound terms
    arguments.cY0LowerS arguments.cY0LowerY
  cY0Upper : points.cY0Upper.Sound terms
    arguments.cY0UpperS arguments.cY0UpperY
  aELower : points.aELower.Sound terms
    arguments.aELowerS arguments.aELowerY
  aEUpper : points.aEUpper.Sound terms
    arguments.aEUpperS arguments.aEUpperY
  cELower : points.cELower.Sound terms
    arguments.cELowerS arguments.cELowerY
  cEUpper : points.cEUpper.Sound terms
    arguments.cEUpperS arguments.cEUpperY

/-- Promote shared point facts to the endpoint theorem used by the
point-cached evaluator.  `harguments` is the leaf's single authenticated
box-geometry normalization. -/
theorem EndpointPointValues.toEndpointSound (bits terms : ℕ)
    {box : CertificateBox} {arguments : Arguments}
    {points : EndpointPointValues}
    (harguments : arguments = LRUpperKCachedScalarArguments.exact box)
    (hpoints : points.Sound terms arguments) :
    EndpointSound box (points.scalarValues bits arguments) := by
  subst arguments
  refine
    { aY0Lower := ?_
      aY0Upper := ?_
      cY0Lower := ?_
      cY0Upper := ?_
      aELower := ?_
      aEUpper := ?_
      cELower := ?_
      cEUpper := ?_ }
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      APointValues.enclosure_sound bits terms hpoints.aY0Lower
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      APointValues.enclosure_sound bits terms hpoints.aY0Upper
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      CPointValues.enclosure_sound bits terms hpoints.cY0Lower
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      CPointValues.enclosure_sound bits terms hpoints.cY0Upper
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      APointValues.enclosure_sound bits terms hpoints.aELower
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      APointValues.enclosure_sound bits terms hpoints.aEUpper
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      CPointValues.enclosure_sound bits terms hpoints.cELower
  · simpa only [EndpointPointValues.scalarValues,
      LRUpperKCachedScalarArguments.exact] using
      CPointValues.enclosure_sound bits terms hpoints.cEUpper

end LRUpperKPointEndpointAssembly
end CourtadeKumar
