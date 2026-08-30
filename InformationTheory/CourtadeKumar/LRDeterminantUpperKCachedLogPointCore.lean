import InformationTheory.CourtadeKumar.LRCertificateQEnclosure
import InformationTheory.CourtadeKumar.LRDeterminantUpperKDyadicOuterRoundingCore

/-!
# Lightweight cached-log point computations

This module contains only the data and rational computations needed by the
generated upper-`K` point queries.  Semantic containment proofs live in
`LRDeterminantUpperKCachedLogPointCertificate`, so query compilation does not
need to import the historical scalar-soundness stack.
-/

namespace CourtadeKumar
namespace LRUpperKCachedLogPointCore

/-- The pair of scalar enclosures cached at one rational point. -/
structure Values where
  q : RationalEnclosure
  qPrime : RationalEnclosure

/-- The two logarithm enclosures shared by the `Q` and `Q'` formulas. -/
structure LogValues where
  lower : RationalEnclosure
  upper : RationalEnclosure

/-- Evaluate both point scalars from one pair of cached logarithm enclosures. -/
def rawValues (certificate : LRQPointCertificate) (logs : LogValues) : Values :=
  { q := RationalEnclosure.neg <| RationalEnclosure.add
      (RationalEnclosure.mul certificate.lowerProbability logs.lower)
      (RationalEnclosure.mul certificate.upperProbability logs.upper)
    qPrime := RationalEnclosure.scale (1 / 4) <| RationalEnclosure.div
      (RationalEnclosure.sub logs.upper logs.lower)
      certificate.sqrtEnclosure }

/-- Round both raw point enclosures outward to a bounded dyadic width. -/
def outerValues (bits : ℕ) (values : Values) : Values :=
  { q := LRUpperKDyadicOuterRounding.outerEnclosure bits values.q
    qPrime := LRUpperKDyadicOuterRounding.outerEnclosure bits values.qPrime }

end LRUpperKCachedLogPointCore
end CourtadeKumar
