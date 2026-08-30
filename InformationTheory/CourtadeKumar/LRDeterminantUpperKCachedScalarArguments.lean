import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedCornerValues

/-!
# Exact scalar arguments for reusable upper-`K` corner caches

Generated leaves authenticate the sixteen rational `(s,y)` coordinates of a
center or whole box once.  Scalar cache covers can then be attached fieldwise,
without normalizing the box geometry again for every endpoint.
-/

namespace CourtadeKumar
namespace LRUpperKCachedScalarArguments

open LRUpperKReplayCertificate

structure Arguments where
  aY0LowerS : ℚ
  aY0LowerY : ℚ
  aY0UpperS : ℚ
  aY0UpperY : ℚ
  cY0LowerS : ℚ
  cY0LowerY : ℚ
  cY0UpperS : ℚ
  cY0UpperY : ℚ
  aELowerS : ℚ
  aELowerY : ℚ
  aEUpperS : ℚ
  aEUpperY : ℚ
  cELowerS : ℚ
  cELowerY : ℚ
  cEUpperS : ℚ
  cEUpperY : ℚ

def exact (box : CertificateBox) : Arguments :=
  { aY0LowerS := box.sHi
    aY0LowerY := (y0AD box).value.lower
    aY0UpperS := box.sLo
    aY0UpperY := (y0AD box).value.upper
    cY0LowerS := box.sHi
    cY0LowerY := (y0AD box).value.upper
    cY0UpperS := box.sLo
    cY0UpperY := (y0AD box).value.lower
    aELowerS := box.sHi
    aELowerY := (eAD box).value.lower
    aEUpperS := box.sLo
    aEUpperY := (eAD box).value.upper
    cELowerS := box.sHi
    cELowerY := (eAD box).value.upper
    cEUpperS := box.sLo
    cEUpperY := (eAD box).value.lower }

structure Covers (terms sqrtFuel logFuel : ℕ) (arguments : Arguments)
    (values : LRUpperKCachedCornerValues.ScalarValues) : Prop where
  aY0Lower : LRUpperKMidpointCoarsening.Covers values.aY0Lower
    (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
      arguments.aY0LowerS arguments.aY0LowerY)
  aY0Upper : LRUpperKMidpointCoarsening.Covers values.aY0Upper
    (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
      arguments.aY0UpperS arguments.aY0UpperY)
  cY0Lower : LRUpperKMidpointCoarsening.Covers values.cY0Lower
    (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
      arguments.cY0LowerS arguments.cY0LowerY)
  cY0Upper : LRUpperKMidpointCoarsening.Covers values.cY0Upper
    (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
      arguments.cY0UpperS arguments.cY0UpperY)
  aELower : LRUpperKMidpointCoarsening.Covers values.aELower
    (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
      arguments.aELowerS arguments.aELowerY)
  aEUpper : LRUpperKMidpointCoarsening.Covers values.aEUpper
    (LRUpperKHistoricalACValues.aAutoI terms sqrtFuel logFuel
      arguments.aEUpperS arguments.aEUpperY)
  cELower : LRUpperKMidpointCoarsening.Covers values.cELower
    (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
      arguments.cELowerS arguments.cELowerY)
  cEUpper : LRUpperKMidpointCoarsening.Covers values.cEUpper
    (LRUpperKHistoricalACValues.cAutoI terms sqrtFuel logFuel
      arguments.cEUpperS arguments.cEUpperY)

theorem coversExact_auto (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (arguments : Arguments)
    (values : LRUpperKCachedCornerValues.ScalarValues)
    (harguments : arguments = exact box)
    (hcovers : Covers terms sqrtFuel logFuel arguments values) :
    LRUpperKCachedCornerValues.CoversExact terms box
      (LRUpperKExplicitCornerPayload.auto sqrtFuel logFuel box)
      values.assemble := by
  subst arguments
  exact LRUpperKCachedCornerValues.coversExact_auto
    terms sqrtFuel logFuel box values
    hcovers.aY0Lower hcovers.aY0Upper
    hcovers.cY0Lower hcovers.cY0Upper
    hcovers.aELower hcovers.aEUpper
    hcovers.cELower hcovers.cEUpper

end LRUpperKCachedScalarArguments
end CourtadeKumar
