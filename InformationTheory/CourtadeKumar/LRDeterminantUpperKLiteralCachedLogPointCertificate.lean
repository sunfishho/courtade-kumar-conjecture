import InformationTheory.CourtadeKumar.LRDeterminantUpperKLiteralCachedLogPointCore
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

abbrev Sound := LRUpperKPointCache.Sound

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

/-- Promote lightweight arithmetic facts to a semantic certified point.

Generated arithmetic shards deliberately avoid importing this semantic layer.
Replay leaves import it once and promote only the exact points they use. -/
def certifiedPoint_of_atomic_outer_eq
    (pointBits logBits terms : ℕ) {z : ℚ}
    {certificate : LRQPointCertificate} {logs : LogValues} {values : Values}
    (checks : LRQPointCertificate.AtomicChecks z certificate)
    (outer : OuterEqualities pointBits logBits terms certificate logs values) :
    LRUpperKPointCache.CertifiedPoint terms z :=
  { values := values
    sound := sound_of_atomic_outer_eq pointBits logBits terms checks outer }

end LRUpperKLiteralCachedLogPointCertificate
end CourtadeKumar
