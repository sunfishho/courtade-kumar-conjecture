import InformationTheory.CourtadeKumar.LRCompactVStagedGroupedGeneratedCertificate
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
# Kernel replay canary for the 192-term grouped fallback

This small box is closed by the grouped fallback after the direct checker
fails.  It exercises the actual exact-rational Lean evaluator at the chosen
head length before any large certificate tree is emitted.
-/

set_option autoImplicit false

namespace CourtadeKumar

def lrCompactVLambdaGroupedCanaryBox : CertificateBox where
  sLo := 921 / 1024
  sHi := 9 / 10
  kLo := 481 / 512
  kHi := 241 / 256
  chiLo := 63 / 64
  chiHi := 505 / 512

def lrCompactVLambdaGroupedCanaryCertificate :
    LRCompactVLambdaGroupedLeafCertificate :=
  LRCompactVLambdaGroupedLeafCertificate.auto
    16 lrCompactVLambdaGroupedCanaryBox

#kernel_checked_bool lrCompactVLambdaGroupedCanary_check
  (lrCompactVLambdaGroupedCanaryCertificate.check
    34 64 34 lrCompactVLambdaGroupedCanaryBox)

theorem lrCompactVLambdaGroupedCanary_sound :
    ∀ point, lrCompactVLambdaGroupedCanaryBox.Contains point →
      LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVLambdaGroupedCanaryCertificate.sound
    34 64 34 lrCompactVLambdaGroupedCanary_check

end CourtadeKumar
