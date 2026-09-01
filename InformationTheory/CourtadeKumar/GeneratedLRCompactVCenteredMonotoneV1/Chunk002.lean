import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Config
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
Kernel arithmetic replay chunk 002; leaves [4, 5].
Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

open LRCompactVCenteredMonotoneLeaf

def leaf4Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box4 row4

#kernel_checked_bool leaf4Check leaf4Result

def leaf4Checked : CheckedTree box4 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row4 leaf4Check

def leaf5Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box5 row5

#kernel_checked_bool leaf5Check leaf5Result

def leaf5Checked : CheckedTree box5 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row5 leaf5Check

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
