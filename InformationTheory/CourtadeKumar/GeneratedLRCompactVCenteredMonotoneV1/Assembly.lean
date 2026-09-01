import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Chunk000
import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Chunk001
import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Chunk002
import InformationTheory.CourtadeKumar.GeneratedLRCompactVCenteredMonotoneV1.Chunk003

/-!
Arithmetic-free assembly of the eight independently kernel-checked leaves.
The joins reproduce the audited balanced k-subdivision exactly.

Design SHA-256: 5b48a177063dc0dde6e42d266b0649b9c338353987a60fb27135c1dc791f1325
Observation SHA-256: 43eaa0d8dd4f406b5b4b1922d9832bfbe70139185d99dbae1079e672982c3421
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVCenteredMonotoneV1

open LRCompactVCenteredMonotoneLeaf

def nodeLL : CheckedTree boxLL :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut1 leaf0Checked leaf1Checked

def nodeLR : CheckedTree boxLR :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut3 leaf2Checked leaf3Checked

def nodeL : CheckedTree boxL :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut2 nodeLL nodeLR

def nodeRL : CheckedTree boxRL :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut5 leaf4Checked leaf5Checked

def nodeRR : CheckedTree boxRR :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut7 leaf6Checked leaf7Checked

def nodeR : CheckedTree boxR :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut6 nodeRL nodeRR

def checked : CheckedTree rootBox :=
  LRCompactVCenteredMonotoneCheckedTree.CheckedTree.join
    .k cut4 nodeL nodeR

def certificate : SubdivisionCertificate Row Unit :=
  checked.certificate

theorem certificateCheck :
    certificate.check
      (Row.checkAt logTerms halfLogTerms dTerms)
      LRCompactVCenteredMonotoneCheckedTree.noDiscard rootBox = true := by
  exact checked.checked

end GeneratedLRCompactVCenteredMonotoneV1
end CourtadeKumar
