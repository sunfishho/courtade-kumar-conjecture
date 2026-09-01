import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Assembly
import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneCheckedTree

/-!
Semantic endpoint of the generated centered-monotone certificate.
Its only arithmetic inputs are the eight kernel theorems imported through
Assembly; this module performs no certificate computation.

Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

theorem target_nonnegative :
    ∀ point, rootBox.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.target_nonnegative checked

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
