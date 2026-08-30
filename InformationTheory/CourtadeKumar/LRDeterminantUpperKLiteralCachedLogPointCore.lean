import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedLogPointCore

/-!
# Arithmetic core for literal cached-log point certificates

Generated arithmetic shards prove only the equalities in `OuterEqualities`.
Semantic containment and checker assembly live in
`LRDeterminantUpperKLiteralCachedLogPointCertificate`.
-/

namespace CourtadeKumar
namespace LRUpperKLiteralCachedLogPointCertificate

abbrev LogValues := LRUpperKCachedLogPointCore.LogValues
abbrev Values := LRUpperKCachedLogPointCore.Values

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
        (LRUpperKCachedLogPointCore.rawValues certificate logs).q
  qPrime : values.qPrime =
      LRUpperKDyadicOuterRounding.outerEnclosure pointBits
        (LRUpperKCachedLogPointCore.rawValues certificate logs).qPrime

end LRUpperKLiteralCachedLogPointCertificate
end CourtadeKumar
