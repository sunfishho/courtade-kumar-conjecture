import InformationTheory.CourtadeKumar.GeneratedLRCompactVAdjacentStagedReplayV1.Config

set_option autoImplicit false

namespace CourtadeKumar
namespace GeneratedLRCompactVAdjacentStagedReplayV1

def leaf052Data : LRCompactVStagedGroupedLeafCertificate :=
  .sameY
    { logOnePlusVHi := { exponent := 0, mantissa := ((63 : ℚ) / 32) }
      headChoice := .n192 }

#kernel_checked_bool leaf052Check
  (leaf052Data.check logTerms pZeroTerms wTerms dTerms directN box_rRRRRRR)

def leaf052Checked : CheckedTree box_rRRRRRR :=
  LRCompactVStagedGroupedCheckedTree.ofAccept
    logTerms pZeroTerms wTerms dTerms directN
    leaf052Data leaf052Check

end GeneratedLRCompactVAdjacentStagedReplayV1
end CourtadeKumar
