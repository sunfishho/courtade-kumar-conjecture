import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Config
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand

/-!
Kernel arithmetic replay chunk 003; leaves [6, 7].
Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

open LRCompactVCenteredMonotoneLeaf

def leaf6Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box6 row6

#kernel_checked_bool leaf6Check leaf6Result

def leaf6Checked : CheckedTree box6 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row6 leaf6Check

def leaf7Result : Bool :=
  Row.checkAt logTerms halfLogTerms dTerms box7 row7

#kernel_checked_bool leaf7Check leaf7Result

def leaf7Checked : CheckedTree box7 :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.ofAccept
    logTerms halfLogTerms dTerms row7 leaf7Check

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
