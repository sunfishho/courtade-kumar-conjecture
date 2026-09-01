import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Config
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
Kernel arithmetic replay chunk 000; leaves [0, 1].
Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

open LRCompactVCenteredMonotoneLeaf

def leaf0Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box0 row0

#kernel_checked_bool leaf0Check leaf0Result

def leaf0Checked : CheckedTree box0 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row0 leaf0Check

def leaf1Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box1 row1

#kernel_checked_bool leaf1Check leaf1Result

def leaf1Checked : CheckedTree box1 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row1 leaf1Check

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
