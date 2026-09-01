import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Config
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
Kernel arithmetic replay chunk 001; leaves [2, 3].
Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

open LRCompactVCenteredMonotoneLeaf

def leaf2Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box2 row2

#kernel_checked_bool leaf2Check leaf2Result

def leaf2Checked : CheckedTree box2 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row2 leaf2Check

def leaf3Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box3 row3

#kernel_checked_bool leaf3Check leaf3Result

def leaf3Checked : CheckedTree box3 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row3 leaf3Check

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
