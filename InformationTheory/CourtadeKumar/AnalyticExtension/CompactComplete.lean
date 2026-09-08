import InformationTheory.CourtadeKumar.AnalyticExtension.CompactCheckerSound
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactCoverage
import InformationTheory.CourtadeKumar.LRCompactVPartialCover

/-! The complete compact-V domain, with an explicit t²-to-t coordinate bridge.
Concrete batch checks use kernel-checked integer interval arithmetic,
connected to the real-valued statement by the interval soundness proof. -/
open Set
namespace CourtadeKumar.LRCompactReducedCertificate


theorem full : LRCompactVSoundLedger := by
  constructor
  intro R v t hR hRhi hv hvthird ht htsq hJ
  have htLower : (9/10:ℝ) ≤ t := by
    by_contra h
    have hs := mul_self_lt_mul_self ht.1.le (lt_of_not_ge h)
    nlinarith
  have hp : root.Contains ⟨R,v,t⟩ := by
    norm_num [root, CertificateBox.Contains]
    exact ⟨hR.1.le,hRhi,hvthird,hv.2.le,htLower,ht.2.le⟩
  exact root_sound _ hp
    ⟨⟨hR.1,hRhi⟩,hv,hvthird,ht,hJ⟩

/-- The stronger full result supplies the existing residual-ledger interface,
regardless of which earlier partial boxes are retained downstream. -/
theorem residual (boxes : List CertificateBox) : LRCompactVResidualLedger boxes := by
  constructor
  intro R v t hR hRhi hv hvthird ht htsq hJ _
  exact full.v_nonnegative R v t hR hRhi hv hvthird ht htsq hJ

end CourtadeKumar.LRCompactReducedCertificate
