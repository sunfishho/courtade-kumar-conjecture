import InformationTheory.CourtadeKumar.LRDeterminantUpperKCachedLogPointCore
import InformationTheory.CourtadeKumar.LRDeterminantUpperKEnclosureCovers
import InformationTheory.CourtadeKumar.LRCertificateQPointSound

/-!
# Lightweight semantic core for upper-`K` point certificates

Generated point-cache modules need only the paired `Q/Q'` enclosure type and
its semantic containment statement.  Keeping those declarations here avoids
loading the historical `A/C` scalar-soundness stack into every generated point
proof.  The higher-level `LRDeterminantUpperKPointCache` module extends this
same namespace with the `A/C` operations.
-/

namespace CourtadeKumar
namespace LRUpperKPointCache

open Set
open LRUpperKMidpointCoarsening

abbrev Values := LRUpperKCachedLogPointCore.Values

structure Sound (terms : ℕ) (z : ℚ) (values : Values) : Prop where
  q : values.q.Contains (lrCertificateQ (z : ℝ))
  qPrime : values.qPrime.Contains (lrCertificateQPrime (z : ℝ))

/-- A point-cache entry keeps its enclosure data separate from its semantic
proof, so evaluation never traverses proof fields. -/
structure CertifiedPoint (terms : ℕ) (z : ℚ) where
  values : Values
  sound : Sound terms z values

/-- One serialized point certificate supplies both cached scalar nodes. -/
theorem sound_of_certificate (terms : ℕ) {z : ℚ}
    {certificate : LRQPointCertificate} {values : Values}
    (hz : z ∈ Ioo (0 : ℚ) 1)
    (hcheck : certificate.primeCheck z = true)
    (hq : Covers values.q (certificate.enclosure terms))
    (hqPrime : Covers values.qPrime (certificate.primeEnclosure terms)) :
    Sound terms z values := by
  have hparts : certificate.check z = true ∧
      (0 : ℚ) < certificate.sqrtEnclosure.lower := by
    simpa [LRQPointCertificate.primeCheck] using hcheck
  exact
    { q := contains_of_covers hq (certificate.sound terms hparts.1)
      qPrime := contains_of_covers hqPrime
        (certificate.prime_sound terms hz hcheck) }

end LRUpperKPointCache
end CourtadeKumar
