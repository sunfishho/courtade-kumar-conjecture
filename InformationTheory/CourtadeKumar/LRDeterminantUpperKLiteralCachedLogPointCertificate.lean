import InformationTheory.CourtadeKumar.LRDeterminantQPointCertificateAtomicCheck
import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedLogPointCertificate

/-!
# Stack-safe assembly for literal cached-log point certificates

Generated point-cache modules authenticate six atomic checker facts and four
independent outward-rounding equalities.  This module performs the shared
semantic assembly once, without reducing a complete point checker or a paired
`Q/Q'` value record.
-/

namespace CourtadeKumar
namespace LRUpperKLiteralCachedLogPointCertificate

open LRUpperKMidpointCoarsening

abbrev LogValues := LRUpperKCachedLogPointCertificate.LogValues
abbrev Values := LRUpperKPointCache.Values
abbrev Sound := LRUpperKPointCache.Sound

/-- Four independent outward-rounding equalities for the literal cached logs
and point values.  Generated code uses one record declaration but still gives
each field its own bounded reduction goal. -/
structure OuterEqualities (pointBits logBits terms : ℕ)
    (certificate : LRQPointCertificate) (logs : LogValues)
    (values : Values) : Prop where
  logLower : logs.lower =
      LRUpperKDyadicOuterRounding.outerEnclosure logBits
        (certificate.logLowerProbability.enclosure terms)
  logUpper : logs.upper =
      LRUpperKDyadicOuterRounding.outerEnclosure logBits
        (certificate.logUpperProbability.enclosure terms)
  q : values.q =
      LRUpperKDyadicOuterRounding.outerEnclosure pointBits
        (LRUpperKCachedLogPointCertificate.rawValues certificate logs).q
  qPrime : values.qPrime =
      LRUpperKDyadicOuterRounding.outerEnclosure pointBits
        (LRUpperKCachedLogPointCertificate.rawValues certificate logs).qPrime

/-- Componentwise outward-rounding equalities, together with the atomic
certificate facts, imply semantic soundness of the literal point values. -/
theorem sound_of_atomic_outer_eq
    (pointBits logBits terms : ℕ) {z : ℚ}
    {certificate : LRQPointCertificate} {logs : LogValues} {values : Values}
    (checks : LRQPointCertificate.AtomicChecks z certificate)
    (outer : OuterEqualities pointBits logBits terms certificate logs values) :
    Sound terms z values := by
  have hlogs :
      LRUpperKCachedLogPointCertificate.LogValues.Covers
        terms certificate logs := by
    constructor
    · rw [outer.logLower]
      exact LRUpperKDyadicOuterRounding.outerEnclosure_covers logBits _
    · rw [outer.logUpper]
      exact LRUpperKDyadicOuterRounding.outerEnclosure_covers logBits _
  have hraw := LRUpperKCachedLogPointCertificate.rawValues_sound terms
    checks.inRange checks.toPrimeCheck hlogs
  refine { q := ?_, qPrime := ?_ }
  · exact contains_of_covers (by
      rw [outer.q]
      exact LRUpperKDyadicOuterRounding.outerEnclosure_covers pointBits _)
      hraw.q
  · exact contains_of_covers (by
      rw [outer.qPrime]
      exact LRUpperKDyadicOuterRounding.outerEnclosure_covers pointBits _)
      hraw.qPrime

end LRUpperKLiteralCachedLogPointCertificate
end CourtadeKumar
