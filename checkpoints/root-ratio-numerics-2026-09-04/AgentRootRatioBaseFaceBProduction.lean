import AgentRootRatioBaseFaceBStandalone
import InformationTheory.CourtadeKumar.LRHighShapeABAssembly

/-! Production-name bridge for the independently checked B interval.
The full D9 evaluator and automatic payloads are not imported. -/

set_option autoImplicit false

namespace CourtadeKumar.RootRatioBaseFaceBStandalone

open RationalEnclosure RootRatioBaseFaceRoundedPilot RootRatioBaseFaceD1Standalone

theorem production_rounded_contains {p : CertificatePoint}
    (hs : p.s = 1 / 16)
    (hk : (767 / 256 : ℝ) ≤ p.k ∧ p.k ≤ 769 / 256)
    (hc : (767 / 2048 : ℝ) ≤ p.chi ∧ p.chi ≤ 769 / 2048) :
    pilot8Bounds.b.Contains (lrCertificateBFlow p) := by
  have hsI : sI.Contains p.s := by norm_num [sI, point, Contains, hs]
  have hkI : kI.Contains p.k := by simpa [kI, Contains] using hk
  have hcI : chiI.Contains p.chi := by simpa [chiI, Contains] using hc
  simpa only [bValue, lrCertificateBFlow, lrCertificateBFlowValue,
    lrCertificateB, lrCertificateE, lrCertificateV, lrCertificateX] using
    rounded_contains hsI hkI hcI

theorem production_positive {p : CertificatePoint}
    (hs : p.s = 1 / 16)
    (hk : (767 / 256 : ℝ) ≤ p.k ∧ p.k ≤ 769 / 256)
    (hc : (767 / 2048 : ℝ) ≤ p.chi ∧ p.chi ≤ 769 / 2048) :
    0 < lrCertificateBFlow p := by
  have h := (production_rounded_contains hs hk hc).1
  have hlo : (0 : ℝ) < (pilot8Bounds.b.lower : ℝ) := by norm_num [pilot8Bounds]
  exact hlo.trans_le h

#print axioms CourtadeKumar.RootRatioBaseFaceBStandalone.production_rounded_contains
#print axioms CourtadeKumar.RootRatioBaseFaceBStandalone.production_positive

end CourtadeKumar.RootRatioBaseFaceBStandalone
