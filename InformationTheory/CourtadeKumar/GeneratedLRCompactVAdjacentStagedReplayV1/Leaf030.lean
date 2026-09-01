import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf030Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((1003 : ℚ) / 512) }
      headChoice := .n128 }

#kernel_checked_bool leaf030Check
  (leaf030Data.check logTerms pZeroTerms wTerms dTerms directN box_rRLRRLL)

def leaf030Checked : CheckedTree box_rRLRRLL :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf030Data leaf030Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
