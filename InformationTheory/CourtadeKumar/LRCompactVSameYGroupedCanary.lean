import InformationTheory.CourtadeKumar.LRCompactVSameYGroupedLeafChecker
import InformationTheory.CourtadeKumar.LRCompactVHybridDirectDGeneratedCertificate
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
# Kernel replay canary for the same-`y` grouped leaf

This box exercises the tight endpoint `D/B` ratio, its rational slope check,
the reduced 128-term grouped head, and the ordinary kernel soundness bridge.
-/

set_option autoImplicit false

namespace CourtadeKumar

def lrCompactVSameYGroupedCanaryBox : CertificateBox where
  sLo := 921 / 1024
  sHi := 9 / 10
  kLo := 481 / 512
  kHi := 241 / 256
  chiLo := 63 / 64
  chiHi := 505 / 512

def lrCompactVSameYGroupedCanaryB : LRCompactVBCertificate :=
  LRCompactVBCertificate.hybridDirectDAuto
    16 lrCompactVSameYGroupedCanaryBox

def lrCompactVSameYGroupedCanaryCertificate :
    LRCompactVSameYGroupedLeafCertificate :=
  { logOnePlusVHi := lrCompactVSameYGroupedCanaryB.logOnePlusV.upper
    headChoice := .n128 }

#kernel_checked_bool lrCompactVSameYGroupedCanary_check
  (lrCompactVSameYGroupedCanaryCertificate.check
    34 64 34 lrCompactVSameYGroupedCanaryBox)

theorem lrCompactVSameYGroupedCanary_sound :
    ∀ point, lrCompactVSameYGroupedCanaryBox.Contains point →
      LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVSameYGroupedCanaryCertificate.sound
    34 64 34 lrCompactVSameYGroupedCanary_check

end CourtadeKumar
